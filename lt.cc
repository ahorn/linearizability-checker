// Alex Horn, University of Oxford
//
// The source code is structured into three main parts:
//
// 1) Data structures and algorithm of the linearizability tester,
//    including a new optional partitioning algorithm;
//
// 2) Immutable data types for sets, registers and stacks with
//    efficient equality checks;
//
// 3) Unit tests and experiments with TBB, EMBB, and etcd.
#include <thread>
#include <atomic>
#include <tuple>
#include <memory>
#include <vector>
#include <climits>
#include <cstddef>
#include <utility>
#include <cassert>
#include <type_traits>
#include <unordered_set>
#include <unordered_map>
#include <fstream>
#include <sstream>
#include <string>
#include <stdexcept>
#include <list>

// functional testing and experiments
#include <random>
#include <functional>
#include <iostream>

/// Allow users to print out counterexamples
#define _LT_DEBUG_

#ifdef _LT_DEBUG_
#include <string>
#include <ostream>
#include <sstream>
#include <string>
#include <algorithm>
#endif

#ifdef _ENABLE_EMBB_
#define _LT_TIMEOUT_
#include <embb/base/thread.h>
#include <embb/containers/lock_free_stack.h>
#endif

#ifdef _ENABLE_TBB_
#define _LT_TIMEOUT_
#include "tbb/concurrent_unordered_set.h"
#endif

#ifdef __linux__
#define _LT_MEM_USAGE_
#endif

#ifdef _LT_TIMEOUT_
#include <chrono>
#endif

#ifdef _LT_MEM_USAGE_
#include <unistd.h>
#include <ios>
#include <iostream>
#include <algorithm>
#endif

#if __cplusplus <= 201103L
// since C++14 in std, see Herb Sutter's blog
template<class T, class ...Args>
std::unique_ptr<T> make_unique(Args&& ...args)
{
  return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
}
#else
  using std::make_unique;
#endif

/// Linearizability tester
namespace lt
{

/************* Core data structures and algorithms *************/

template<class S>
class Entry;

/// Doubly-linked list of log entries

/// S - sequential data type
template<class S>
using EntryPtr = Entry<S>*;

/// Bounded stack of call entries that have been linearized

/// S - sequential data type
template<class S>
class Stack
{
private:
  typedef std::tuple<EntryPtr<S>, S> Pair;
  typedef std::vector<Pair> Pairs;
  typedef typename Pairs::size_type SizeType;

  // A constant-size vector
  Pairs m_vector;
  SizeType m_top;

public:
  /// Create a new stack of bounded height

  /// \post: if capacity is positive, then not is_full()
  Stack(SizeType capacity)
  : m_vector(capacity), m_top{0U}
  {
    assert(capacity == 0U or not is_full());
  }

  /// Number of entries in the stack
  SizeType size() const noexcept
  {
    return m_top;
  }

  /// Is size() zero?
  bool is_empty() const noexcept
  {
    return 0U == size();
  }

  /// Is size() equal to the stack's capacity?
  bool is_full() const noexcept
  {
    return m_top == m_vector.size();
  }

  /// \pre: not is_empty()
  const Pair& top() const noexcept
  {
    assert(not is_empty());
    return m_vector[m_top - 1U];
  }

  /// Add an entry to the top() of the stack

  /// \pre: not is_full()
  /// \pre: ptr->is_call()
  void push(EntryPtr<S>, S&&);

  /// Remove count entries from the stack

  /// \pre: 0 < count <= size()
  void pop(unsigned count = 1U)
  {
    assert(0U < count);
    assert(count <= size());

    m_top -= count;
  }

  /// \internal
  EntryPtr<S> entry_ptr(std::size_t pos)
  {
    assert(pos < m_top);
    return std::get<0>(m_vector[pos]);
  }
};

template<class S> class Entry;
template<class S> class Log;
template<class S> class ConcurrentLog;
template<class S> class Slicer;
template<class S, bool> class LinearizabilityTester;

/// A kind of "functor" in C++ terminology

/// S - sequential data type
template<class S>
class Op
{
private:
  friend class Entry<S>;

  // Is m_partition defined?
  bool m_is_partitionable;
  unsigned m_partition;

  // modified by Entry
  unsigned ref_counter;

#ifdef _LT_DEBUG_
  virtual std::ostream& print(std::ostream&) const = 0;
#endif

  virtual std::pair<bool, S> internal_apply(const S&, const Op<S>&)
  {
    return {};
  }

public:
  Op()
  : m_is_partitionable{false},
    m_partition{0U},
    ref_counter{0U} {}

  Op(unsigned partition)
  : m_is_partitionable{true},
    m_partition{partition},
    ref_counter{0U} {}

  Op(bool is_partitionable, unsigned partition)
  : m_is_partitionable{is_partitionable},
    m_partition{partition},
    ref_counter{0U} {}

  virtual ~Op()
  {
    assert(ref_counter == 0);
  }

  /// Is partition() defined?
  bool is_partitionable() const noexcept
  {
    return m_is_partitionable;
  }

  /// \pre: is_partitionable()
  unsigned partition() const
  {
    assert(m_is_partitionable);
    return m_partition;
  }

  /// Returns true exactly if the operation could be applied
  std::pair<bool, S> apply(const S& s, const Op<S>& op)
  {
    return internal_apply(s, op);
  }

#ifdef _LT_DEBUG_
  friend std::ostream& operator<<(std::ostream& os, const Op& op)
  {
    return op.print(os);
  }
#endif
};

/// Fixed-size set of bits with persistence features
class Bitset
{
public:
  typedef std::size_t Pos;

private:
  friend struct BitsetHash;
  friend class FlexibleBitset;

  typedef unsigned long Block;
  typedef std::vector<Block> Blocks;
  typedef Blocks::size_type BlockIndex;

  /// Accessible bits in a Block
  typedef unsigned BlockWidth;

  static constexpr BlockWidth s_bits_per_block =
    static_cast<BlockWidth>(sizeof(Block) * CHAR_BIT);

  static BlockIndex block_index(Pos pos) noexcept
  {
    return pos / s_bits_per_block;
  }

  static BlockIndex blocks_size(Pos max_pos) noexcept
  {
    return block_index(max_pos) + 1U;
  }

  static BlockWidth bit_index(Pos pos) noexcept
  {
    return static_cast<BlockWidth>(pos % s_bits_per_block);
  }

  static Block bit_mask(Pos pos) noexcept
  {
    return Block(1U) << bit_index(pos);
  }

  /// only resized by FlexibleBitset
  Blocks m_blocks;

  std::size_t m_hash;
  unsigned m_number_of_set_bits;

  Block& find_block(Pos pos)
  {
    BlockIndex i{block_index(pos)};
    assert(i < m_blocks.size());
    return m_blocks[i];
  }

  // We exploit the fact that XOR forms an abelian group:
  // first, clear hash of old block; then, hash new block.
  void update_hash(Block old_block, Block new_block)
  {
    m_hash ^= old_block;
    m_hash ^= new_block;
  }

public:
  Bitset(Pos max_pos)
  : m_blocks(blocks_size(max_pos)),
    m_hash{0U},
    m_number_of_set_bits{0U} {}

  bool is_empty() const noexcept
  {
    return m_number_of_set_bits == 0U;
  }

  bool set(Pos pos)
  {
    Block& block = find_block(pos);
    const Block copy_block{block};
    block |= bit_mask(pos);

    update_hash(copy_block, block);

    bool ok{block != copy_block};
    m_number_of_set_bits += ok;
    return ok;
  }

  Bitset immutable_set(Pos pos) const
  {
    Bitset copy{*this};
    copy.set(pos);
    return copy;
  }

  bool is_set(Pos pos) const
  {
    BlockIndex i{block_index(pos)};
    if (i < m_blocks.size())
      return (m_blocks[i] & bit_mask(pos)) != 0U;

    return false;
  }

  bool reset(Pos pos)
  {
    Block& block = find_block(pos);
    const Block copy_block{block};
    block &= ~bit_mask(pos);

    update_hash(copy_block, block);

    bool ok{block != copy_block};
    m_number_of_set_bits -= ok;
    return ok;
  }

  Bitset immutable_reset(Pos pos) const
  {
    Bitset copy{*this};
    copy.reset(pos);
    return copy;
  }

  // Same number of blocks and identical bits in all those blocks?
  bool operator==(const Bitset& other) const noexcept
  {
    return m_number_of_set_bits == other.m_number_of_set_bits and
      m_blocks == other.m_blocks;
  }

  bool operator!=(const Bitset& other) const noexcept
  {
    return m_number_of_set_bits != other.m_number_of_set_bits or
      m_blocks != other.m_blocks;
  }
};

/// Constant-time, O(1), hash function
struct BitsetHash
{
  std::size_t operator()(const Bitset& bitset) const noexcept
  {
    return bitset.m_hash;
  }
};

/// States of abstract data types
namespace state
{
  template<class T>
  struct Hash
  {
    std::size_t operator()(const T&) const noexcept;
  };
}

template<class S>
using OpPtr = std::unique_ptr<Op<S>>;

/// Call/ret log entry

/// S - sequential data type
template<class S>
class Entry
{
private:
  friend class Log<S>;
  friend class Slicer<S>;
  friend class LinearizabilityTester<S, true>;
  friend class LinearizabilityTester<S, false>;

  // Ref counted pointer because we need to copy logs so that we
  // can experimentally compare different linearizability testers
  //
  // However, this is an implementation detail and the strict type
  // of OpPtr<S> enforces at compile-time that we manage the
  // ownership of these kind of pointers on the user's behalf.
  Op<S>* m_op_ptr;
  unsigned m_entry_id;
  std::thread::id m_thread_id;
  EntryPtr<S> m_match;
  bool m_is_call;

  void inc_ref_counter() const noexcept
  {
    if (m_op_ptr != nullptr)
      ++m_op_ptr->ref_counter;
  }

  void dec_ref_counter() const
  {
    assert(m_op_ptr == nullptr or 0 < m_op_ptr->ref_counter);

    if (m_op_ptr != nullptr and --m_op_ptr->ref_counter == 0)
      delete m_op_ptr;
  }

  /// Log head

  /// \post: if _next is not nullptr, then _next->prev == this
  Entry(EntryPtr<S> _next)
  : m_op_ptr{nullptr},
    m_entry_id{},
    m_thread_id{},
    m_match{nullptr},
    m_is_call{false},
    prev{nullptr},
    next{_next}
  {
    if (_next != nullptr)
      _next->prev = this;
  }

public:
  ~Entry()
  {
    dec_ref_counter();
  }

  EntryPtr<S> prev;
  EntryPtr<S> next;

  Entry()
  : m_op_ptr{nullptr},
    m_entry_id{},
    m_thread_id{},
    m_match{nullptr},
    m_is_call{false},
    prev{nullptr},
    next{nullptr} {}

  Entry(const Entry& entry)
  : m_op_ptr{entry.m_op_ptr},
    m_entry_id{entry.m_entry_id},
    m_thread_id{entry.m_thread_id},
    m_match{entry.m_match},
    m_is_call{entry.m_is_call},
    prev{entry.prev},
    next{entry.next}
  {
    inc_ref_counter();
  }

  Entry& operator=(const Entry& entry)
  {
    entry.inc_ref_counter();
    dec_ref_counter();

    m_op_ptr = entry.m_op_ptr;
    m_entry_id = entry.m_entry_id;
    m_thread_id = entry.m_thread_id;
    m_match = entry.m_match;
    m_is_call = entry.m_is_call;
    prev = entry.prev;
    next = entry.next;

    return *this;
  }

  Entry& operator=(Entry&& entry)
  {
    // only decrement required (due to move semantics)
    dec_ref_counter();

    m_op_ptr = entry.m_op_ptr;
    m_entry_id = entry.m_entry_id;
    m_thread_id = entry.m_thread_id;
    m_match = entry.m_match;
    m_is_call = entry.m_is_call;
    prev = entry.prev;
    next = entry.next;

    entry.m_op_ptr = nullptr;
    entry.m_entry_id = 0;
    entry.m_thread_id = 0;
    entry.m_match = nullptr;
    entry.m_is_call = false;
    entry.prev = nullptr;
    entry.next = nullptr;

    return *this;
  }

  /// \pre: set_match and set_op have been called with non-null arguments
  bool is_partitionable() const
  {
    assert(m_match != nullptr);
    assert(m_match->m_op_ptr != nullptr);
    assert(m_op_ptr->m_is_partitionable == m_match->m_op_ptr->m_is_partitionable);
    assert(m_op_ptr->m_partition == m_match->m_op_ptr->m_partition);

    return m_op_ptr->m_is_partitionable;
  }

  void set_op(OpPtr<S>&& op_ptr) noexcept
  {
    m_op_ptr = op_ptr.release();
    inc_ref_counter();
  }

  Op<S>& op() const
  {
    assert(m_op_ptr != nullptr);
    return *m_op_ptr;
  }

  const Op<S>* const op_ptr() const noexcept
  {
    return m_op_ptr;
  }

  void set_entry_id(unsigned entry_id) noexcept
  {
    m_entry_id = entry_id;
  }

  unsigned entry_id() const noexcept
  {
    return m_entry_id;
  }

  void set_thread_id(std::thread::id thread_id) noexcept
  {
    m_thread_id = thread_id;
  }

  std::thread::id thread_id() const noexcept
  {
    return m_thread_id;
  }

  /// \pre: ret_entry_ptr->match() == nullptr
  /// \pre: not ret_entry_ptr->is_call()
  ///
  /// \post: this->is_call()
  /// \post: this == ret_entry_ptr->match()
  /// \post: this->match() == ret_entry_ptr
  /// \post: this->entry_id() == ret_entry_ptr->entry_id()
  /// \post: if this->is_partitionable() or ret_entry_ptr->is_partitionable(),
  ///        then this->op().partition() == ret_entry_ptr->op().partition()
  void set_match(EntryPtr<S> ret_entry_ptr) noexcept
  {
    assert(ret_entry_ptr->m_match == nullptr);
    assert(not ret_entry_ptr->is_call());

    ret_entry_ptr->m_match = this;
    ret_entry_ptr->set_entry_id(m_entry_id);

    if (ret_entry_ptr->op().m_is_partitionable)
    {
      op().m_is_partitionable = ret_entry_ptr->op().m_is_partitionable;
      op().m_partition = ret_entry_ptr->op().m_partition;
    }
    else
    {
      ret_entry_ptr->op().m_is_partitionable = op().m_is_partitionable;
      ret_entry_ptr->op().m_partition = op().m_partition;
    }

    m_match = ret_entry_ptr;
    m_is_call = true;

    assert(is_call());
    assert(this == ret_entry_ptr->match());
    assert(match() == ret_entry_ptr);
    assert(entry_id() == ret_entry_ptr->entry_id());
    assert(op().m_is_partitionable == ret_entry_ptr->op().m_is_partitionable);
    assert(op().m_partition == ret_entry_ptr->op().m_partition);
  }

  EntryPtr<S> match() const noexcept
  {
    return m_match;
  }

  bool is_call() const noexcept
  {
    return m_is_call;
  }
};

#ifdef _LT_DEBUG_
/// S - sequential data type
template<class S>
std::ostream& operator<<(std::ostream& os, EntryPtr<S> entry_ptr)
{
  if (entry_ptr == nullptr)
    return os << "entry id: none, thread id: none [nullptr]";

  const Entry<S>& entry = *entry_ptr;
  return os <<
    "entry id: " << entry.entry_id() <<
    ", thread id: " << entry.thread_id() <<
    ", " << (entry.is_call() ? "call: " : "return: ") <<
    entry.op();
}
#endif

template<class S>
void Stack<S>::push(EntryPtr<S> ptr, S&& s)
{
  assert(not is_full());
  assert(ptr != nullptr);
  assert(ptr->is_call());

  // no overflow
  m_vector[m_top++] = std::make_pair(ptr, std::move(s));
  assert(0U != m_top);
}

/// Input to linearizabilty testers

/// S - sequential data type
template<class S>
class LogInfo
{
private:
  friend class Slicer<S>;

  EntryPtr<S> m_log_head_ptr;
  std::size_t m_number_of_entries;

public:
  /// \post: is_empty()
  LogInfo() : m_log_head_ptr{nullptr}, m_number_of_entries{0U} {}

  /// \pre: number_of_entries is positive and even
  /// \pre: log_head_ptr is not nullptr
  /// \post: not is_empty()
  LogInfo(EntryPtr<S> log_head_ptr, std::size_t number_of_entries)
  : m_log_head_ptr{log_head_ptr}, m_number_of_entries{number_of_entries}
  {
    assert(log_head_ptr != nullptr);
    assert(0U < m_number_of_entries);
    assert((m_number_of_entries & 1U) == 0U);
  }

  /// Ptr to the first entry in the log
  EntryPtr<S> log_head_ptr() const noexcept
  {
    return m_log_head_ptr;
  }

  /// Even number since every call entry is paired with a return entry
  std::size_t number_of_entries() const noexcept
  {
    return m_number_of_entries;
  }

  bool is_empty() const noexcept
  {
    return m_log_head_ptr == nullptr and m_number_of_entries == 0U;
  }
};

#ifdef _LT_DEBUG_
/// S - sequential data type
template<class S>
std::ostream& operator<<(std::ostream& os, const LogInfo<S>& log_info)
{
  EntryPtr<S> entry_ptr{log_info.log_head_ptr()};

  os << "log info, number of entries: " << log_info.number_of_entries() << std::endl;
  for (; entry_ptr != nullptr; entry_ptr = entry_ptr->next)
    os << entry_ptr << std::endl;

  return os;
}
#endif

/// Bounded history log

/// If you need thread-safety, use ConcurrentLog<S> instead.
///
/// S - sequential data type
template<class S>
class Log
{
private:
  // fixed-size vector
  typedef std::vector<Entry<S>> Entries;

public:
  typedef typename Entries::size_type Size;

private:
  // we never resize the vector and so pointers into it are stable
  Size m_entry_id, m_index;
  Entries m_entries;
  EntryPtr<S> m_last_entry_ptr;

  void link(Entry<S>& entry) noexcept
  {
    if (m_last_entry_ptr != nullptr)
      m_last_entry_ptr->next = &entry;

    entry.prev = m_last_entry_ptr;
  }

public:
  /// A history with at most capacity entries
  Log(Size capacity)
  : m_entry_id{0U},
    m_index{0U},
    m_entries(capacity),
    m_last_entry_ptr{nullptr} {}

  /// Copy entries
  Log(LogInfo<S> log_info)
  : m_entry_id{0U},
    m_index{0U},
    m_entries(log_info.number_of_entries()),
    m_last_entry_ptr{nullptr}
  {
    EntryPtr<S> entry_ptr{log_info.log_head_ptr()};
    std::vector<unsigned> matches(log_info.number_of_entries() >> 1);

    while (entry_ptr != nullptr)
    {
      assert(m_index < m_entries.size());

      Entry<S>& new_entry = m_entries[m_index];
      new_entry = *entry_ptr;
      new_entry.m_match = nullptr;
      link(new_entry);

      if (new_entry.is_call())
      {
        matches[new_entry.entry_id()] = m_index;
      }
      else
      {
        Entry<S>& call_entry = m_entries[matches[new_entry.entry_id()]];
        call_entry.set_match(&new_entry);
      }

      m_last_entry_ptr = &new_entry;
      entry_ptr = entry_ptr->next;
      ++m_index;
    }

    assert(m_index == m_entries.size());
    assert(entry_ptr == nullptr);
  }

  EntryPtr<S> add_call(OpPtr<S>&& op_ptr)
  {
    assert(m_index < m_entries.size());

    Entry<S>& entry = m_entries[m_index++];
    entry.set_op(std::move(op_ptr));
    entry.set_entry_id(m_entry_id++);

    link(entry);
    m_last_entry_ptr = &entry;
    return m_last_entry_ptr;
  }

  /// \post: call_entry_ptr->is_call()
  EntryPtr<S> add_ret(EntryPtr<S> call_entry_ptr, OpPtr<S>&& op_ptr)
  {
    assert(m_index < m_entries.size());

    Entry<S>& entry = m_entries[m_index++];
    entry.set_op(std::move(op_ptr));
    link(entry);

    m_last_entry_ptr = &entry;
    call_entry_ptr->set_match(m_last_entry_ptr);

    assert(call_entry_ptr->is_call());
    assert(m_entry_id <= m_index);

    return m_last_entry_ptr;
  }

  EntryPtr<S> log_head_ptr()
  {
    return &m_entries.front();
  }

  std::size_t number_of_entries() const noexcept
  {
    return m_index;
  }

  LogInfo<S> info()
  {
    return {log_head_ptr(), number_of_entries()};
  }
};

/// Output of linearizability tester

/// S - sequential data type
template<class S>
class Result
{
private:
  friend class LinearizabilityTester<S, true>;
  friend class LinearizabilityTester<S, false>;
  typedef std::vector<EntryPtr<S>> EntryPtrs;

  bool m_is_linearizable;
  EntryPtrs m_entry_ptrs;

#ifdef _LT_DEBUG_
  unsigned m_cutoff_entry_id;
  EntryPtr<S> m_log_head_ptr;
#endif

  bool m_is_timeout;

  double m_virtual_memory_usage;
  double m_resident_set_size;

  void reset()
  {
    m_is_linearizable = true;
    m_entry_ptrs.clear();
#ifdef _LT_DEBUG_
    m_cutoff_entry_id = 0U;
    m_log_head_ptr = nullptr;
#endif
    m_is_timeout = false;
    m_virtual_memory_usage = 0.0;
    m_resident_set_size = 0.0;
  }

public:
  /// Initially linearizable
  Result()
  : m_is_linearizable{true},
    m_entry_ptrs{},
#ifdef _LT_DEBUG_
    m_cutoff_entry_id{0U},
    m_log_head_ptr{nullptr},
#endif
    m_is_timeout{false},
    m_virtual_memory_usage{0.0},
    m_resident_set_size{0.0} {}

  /// \pre: not is_timeout()
  bool is_linearizable() const noexcept
  {
    assert(not is_timeout());
    return m_is_linearizable;
  }

  bool is_timeout() const noexcept
  {
    return m_is_timeout;
  }

  /// Zero if unknown, unit: MiB
  double virtual_memory_usage() const noexcept
  {
    return m_virtual_memory_usage;
  }

  /// Zero if unknown, unit: MiB
  double resident_set_size() const noexcept
  {
    return m_resident_set_size;
  }

#ifdef _LT_DEBUG_
  void debug(std::ostream& os, bool verbose = false)
  {
    os << "Linearizable: ";
    if (m_is_linearizable)
    {
      os << "Yes" << std::endl;
      for (EntryPtr<S> entry_ptr : m_entry_ptrs)
        os << entry_ptr << " : " << entry_ptr->match()  << std::endl;

      return;
    }

    os << "No" << std::endl;
    EntryPtr<S> entry_ptr{m_log_head_ptr};
    for (; entry_ptr != nullptr; entry_ptr = entry_ptr->next)
    {
      os << entry_ptr << std::endl;
      if (entry_ptr->entry_id() == m_cutoff_entry_id)
      {
        os << "^ previous entries cannot be linearized" << std::endl;

        if (not (verbose or entry_ptr->is_call()))
          return;
      }
    }
  }
#endif
};

#ifdef _LT_TIMEOUT_
template <typename Clock = std::chrono::steady_clock>
struct Timeout
{
  const typename Clock::time_point start_time;
  const typename Clock::duration max_duration;

  Timeout()
  : start_time{Clock::now()},
    max_duration{Clock::duration::max()} {}

  Timeout(typename Clock::duration duration)
  : start_time{Clock::now()},
    max_duration{duration} {}

  bool is_expired() const
  {
    return max_duration < (Clock::now() - start_time);
  }
};
#endif

/// Least-recently used cache eviction
template<class Key, class Hash = std::hash<Key>>
class LruCache
{
private:
  typedef std::list<Key> List;
  typedef typename List::iterator ListIterator;
  typedef std::unordered_map<Key, ListIterator, Hash> UnorderedMap;
  typedef typename UnorderedMap::size_type Capacity;

  const Capacity m_capacity;

  UnorderedMap m_unordered_map;
  List m_list;

public:
  typedef typename UnorderedMap::iterator Iterator;

  LruCache()
  : m_capacity{4096},
    m_unordered_map{m_capacity} {}

  LruCache(Capacity capacity)
  : m_capacity{capacity},
    m_unordered_map{m_capacity} {}

  bool insert(Key&& key)
  {
    std::pair<Iterator, bool> pair{m_unordered_map.insert(
      std::make_pair(std::move(key), m_list.end()))};

    if (pair.second)
      pair.first->second = m_list.insert(m_list.cend(), pair.first->first);
    else
      m_list.splice(m_list.end(), m_list, pair.first->second);

    if (m_unordered_map.size() == m_capacity)
    {
      auto iter = m_unordered_map.find(m_list.front());
      assert(iter != m_unordered_map.cend());
      m_unordered_map.erase(iter);
      m_list.pop_front();
    }

    return pair.second;
  }
};

/// S - sequential data type
template<class S, bool enable_cache_eviction = false>
class LinearizabilityTester
{
private:
  // regardless of caching, we need to keep track of the current state of type S
  typedef std::pair<Bitset, S> State;

  // if caching is enabled, we use these hash functions
  class StateHash
  {
  private:
    // courtesy of Daniel Kroening, see CPROVER source file util/irep.cpp
    static inline size_t hash_rotl(std::size_t value, unsigned shift)
    {
      return (value << shift) | (value >> ((sizeof(value) * 8U) - shift));
    }

    // courtesy of Daniel Kroening, see CPROVER source file util/irep.cpp
    static inline size_t hash_combine(std::size_t h1, std::size_t h2)
    {
      return hash_rotl(h1, 7U) ^ h2;
    }

    const BitsetHash m_bitset_hash;
    const state::Hash<S> m_s_hash;

  public:
    StateHash() : m_bitset_hash{}, m_s_hash{} {}

    std::size_t operator()(const State& state) const noexcept
    {
      return hash_combine(m_bitset_hash(state.first), m_s_hash(state.second));
    }
  };

  typedef typename std::conditional<
    /* if */ enable_cache_eviction,
    /* then */ LruCache<State, StateHash>,
    /* else */ std::unordered_set<State, StateHash>>::type StateCache;

  // Maximum number of call/ret entries, i.e. half of the
  // total number of entry pointers reachable in m_log_head
  const std::size_t m_log_size;

  // History to linearize, every call is matched by a return
  const Entry<S> m_log_head;

  // Invariants:
  //
  // * for every EntryPtr<S> `e` in `m_calls`, `e->is_call()` holds
  // * for every EntryPtr<S> `e`, if `e` in `m_calls`, then `e` is not reachable
  //   from `m_log_head` by following the next pointers.
  Stack<S> m_calls;

#ifdef _LT_TIMEOUT_
  Timeout<std::chrono::steady_clock> m_timeout;
#endif

  // An approximation of the workload
  unsigned long m_number_of_iterations;

  // see http://stackoverflow.com/questions/669438/how-to-get-memory-usage-at-run-time-in-c
  //
  // process_mem_usage(double &, double &) - takes two doubles by reference,
  // attempts to read the system-dependent data for a process' virtual memory
  // size and resident set size, and return the results in MiB.
  //
  // On failure, returns 0.0, 0.0
  static void process_mem_usage(double& vm_usage, double& resident_set)
  {
    vm_usage = resident_set = 0.0;

#ifdef _LT_MEM_USAGE_
    // 'file' stat seems to give the most reliable results
    std::ifstream stat_stream("/proc/self/stat", std::ios_base::in);

    // dummy vars for leading entries in stat that we don't care about
    std::string pid, comm, state, ppid, pgrp, session, tty_nr;
    std::string tpgid, flags, minflt, cminflt, majflt, cmajflt;
    std::string utime, stime, cutime, cstime, priority, nice;
    std::string O, itrealvalue, starttime;

    // the two fields we want
    unsigned long vsize;
    long rss;

    stat_stream >> pid >> comm >> state >> ppid >> pgrp >> session >> tty_nr
                >> tpgid >> flags >> minflt >> cminflt >> majflt >> cmajflt
                >> utime >> stime >> cutime >> cstime >> priority >> nice
                >> O >> itrealvalue >> starttime >> vsize >> rss; // don't care about the rest

    stat_stream.close();

    long page_size_kb = sysconf(_SC_PAGE_SIZE) / 1024; // in case x86-64 is configured to use 2MB pages
    vm_usage = vsize / (1024.0 * 1024.0);
    resident_set = (rss * page_size_kb) / 1024.0;
#endif
  }

  // Temporarily remove call_entry_ptr and call_entry_ptr->match() from the log

  // \pre: call_entry_ptr->is_call()
  static void lift(const EntryPtr<S> call_entry_ptr)
  {
    const Entry<S>& call = *call_entry_ptr;
    assert(call.is_call());

    Entry<S>& match = *call.match();
    call.prev->next = call.next;
    call.next->prev = call.prev;
    match.prev->next = match.next;

    if (match.next != nullptr)
      match.next->prev = match.prev;
  }

  // Reinsert call_entry_ptr and call_entry_ptr->match() into the log

  // \pre: call_entry_ptr->is_call()
  static void unlift(const EntryPtr<S> call_entry_ptr)
  {
    const Entry<S>& call = *call_entry_ptr;
    assert(call.is_call());

    Entry<S>& match = *call.match();
    assert(match.prev->next == match.next);
    match.prev->next = &match;

    if (match.next != nullptr)
      match.next->prev = &match;

    assert(call.prev->next == call.next);
    call.prev->next = call_entry_ptr;
    call.next->prev = call_entry_ptr;
  }

  // TODO: Consider pending operations
  static bool cache_state(const S& new_s, const EntryPtr<S>  entry_ptr,
    LruCache<State, StateHash>& state_cache, Bitset& bitset)
  {
    return state_cache.insert(std::make_pair(bitset.immutable_set(entry_ptr->entry_id()), new_s));
  }

  // TODO: Consider pending operations
  static bool cache_state(const S& new_s, const EntryPtr<S>  entry_ptr,
    std::unordered_set<State, StateHash>& state_cache, Bitset& bitset)
  {
    return std::get<1>(state_cache.emplace(bitset.immutable_set(entry_ptr->entry_id()), new_s));
  }

  void internal_check(Result<S>& result, unsigned& global_linearized_entry_id)
  {
    S s, new_s;
    StateCache state_cache;
    bool is_entry_linearizable;
    EntryPtr<S> pop_entry_ptr, entry_ptr{m_log_head.next};

    double virtual_memory_usage;
    double resident_set_size;

    // fixing the size is not merely an optimization but
    // necessary for checking the equality of bitsets
    Bitset linearized_entries(m_log_size);

    while (m_log_head.next != nullptr)
    {
      process_mem_usage(virtual_memory_usage, resident_set_size);
      result.m_virtual_memory_usage = std::max(result.m_virtual_memory_usage, virtual_memory_usage);
      result.m_resident_set_size = std::max(result.m_resident_set_size, resident_set_size);

#ifdef _LT_TIMEOUT_
      if (m_timeout.is_expired())
      {
        result.m_is_timeout = true;
        break;
      }
#endif

      ++m_number_of_iterations;

      assert(entry_ptr != nullptr);
      if (entry_ptr->is_call())
      {
        assert(not m_calls.is_full());
        assert(entry_ptr->match() != nullptr);
        assert(not linearized_entries.is_set(entry_ptr->entry_id()));

        std::tie(is_entry_linearizable, new_s) =
          entry_ptr->op().apply(s, entry_ptr->match()->op());

        if (is_entry_linearizable and cache_state(new_s, entry_ptr, state_cache, linearized_entries))
        {
          // call entry is always matched up with a return entry
          assert(entry_ptr->next != nullptr);

          // provisionally linearize the call entry together with
          // the associated state produced by the new linearization
          m_calls.push(entry_ptr, std::move(s));
          s = std::move(new_s);
          linearized_entries.set(entry_ptr->entry_id());

          // provisionally remove the call and return entry from the history
          lift(entry_ptr);

          // restart from the beginning of the shortened history
          entry_ptr = m_log_head.next;
        }
        else // cannot linearize call entry
        {
          // get the next entry in the unmodified history
          entry_ptr = entry_ptr->next;

#ifdef _LT_DEBUG_
          global_linearized_entry_id = std::max(global_linearized_entry_id, entry_ptr->entry_id());
#endif
        }
      }
      else // handle "return" entry
      {
        if (m_calls.is_empty())
          break;

        assert(not m_calls.is_empty());

        // revert state change
        std::tie(pop_entry_ptr, s) = m_calls.top();
        assert(pop_entry_ptr != nullptr);
        linearized_entries.reset(pop_entry_ptr->entry_id());

        m_calls.pop();

        // undo the provisional linearization
        unlift(pop_entry_ptr);

        // continue after the entry to which we have just backtracked
        entry_ptr = pop_entry_ptr->next;
      }
    }

    // all call entries linearized?
    result.m_is_linearizable = m_calls.is_full();
    assert(result.m_is_linearizable == (m_log_head.next == nullptr));

    // witness linearization
    std::size_t pos{0};
    result.m_entry_ptrs.resize(m_calls.size());
    for (EntryPtr<S>& entry_ptr : result.m_entry_ptrs)
      entry_ptr = m_calls.entry_ptr(pos++);
  }

public:
  LinearizabilityTester(LogInfo<S> log_info)
  : m_log_size{log_info.number_of_entries() >> 1},
    m_log_head{log_info.log_head_ptr()},
    m_calls{m_log_size},
#ifdef _LT_TIMEOUT_
    m_timeout{},
#endif
    m_number_of_iterations{} {}

#ifdef _LT_TIMEOUT_
  LinearizabilityTester(LogInfo<S> log_info,
    std::chrono::steady_clock::duration max_duration)
  : m_log_size{log_info.number_of_entries() >> 1},
    m_log_head{log_info.log_head_ptr()},
    m_calls{m_log_size},
    m_timeout{max_duration},
    m_number_of_iterations{} {}
#endif

  /// A rough approximation of the workload
  unsigned long number_of_iterations() const noexcept
  {
    return m_number_of_iterations;
  }

  /// Is history linearizable?

  /// Throws an exception on timeout
  bool check()
  {
    Result<S> result;
    unsigned disregard_cutoff_entry_id;
    internal_check(result, disregard_cutoff_entry_id);

    if (result.is_timeout())
      throw std::runtime_error("Timeout!");

    return result.is_linearizable();
  }

  void check(Result<S>& result)
  {
    result.reset();

#ifdef _LT_DEBUG_
    internal_check(result, result.m_cutoff_entry_id);
    result.m_log_head_ptr = m_log_head.next;
#else
    unsigned disregard_cutoff_entry_id;
    internal_check(result, disregard_cutoff_entry_id);
#endif
  }
};

/// RAII class to ensure a thread becomes unjoinable on all paths
class Thread
{
private:
  std::thread m_thread;

public:
  Thread()
  : m_thread{} {}

  Thread(std::thread&& thread)
  : m_thread(std::move(thread)) {}

  template<typename F, typename... Args>
  Thread(F&& f, Args&&... args)
  : m_thread(std::forward<F>(f), std::forward<Args>(args)...) {}

  ~Thread()
  {
    if (m_thread.joinable())
      m_thread.join();
  }

  /// \pre: joinable()
  /// \post: not joinable()

  /// Throws std::system_error if an error occurs.
  void join()
  {
    m_thread.join();
  }

  bool joinable() const noexcept
  {
    return m_thread.joinable();
  }

  Thread& operator=(Thread&& thread)
  {
    m_thread = std::move(thread.m_thread);
    return *this;
  }
};

/// Partition history into sub-histories

/// A slicer partitions the history into independent sub-histories.
/// Our partitioning scheme hinges on Theorem 3.6.1 in "The Art of
/// Multiprocessor Programming" (Revised Ed.) by Herlihy and Shavit.
///
/// Typically only associative concurrent abstract data types (ADTs)
/// such as sets and hash tables are suitable for this partitioning
/// scheme. And not all operations on such ADTs are always supported.
/// For example, the partitioning scheme is incompatible with 0-arg
/// operations such as "empty?" on sets. But it is very effective if
/// we want to only check linearizability of say "insert", "remove"
/// and "contains".
///
/// S - sequential data type
template<class S>
class Slicer
{
private:
  typedef std::vector<LogInfo<S>> Sublogs;

  static void slice(const Entry<S>& log_head, Sublogs& sublogs)
  {
    const typename Sublogs::size_type n = sublogs.size();

    EntryPtr<S> entry_ptr{log_head.next}, next_entry_ptr;
    std::vector<EntryPtr<S>> last_entry_ptrs(sublogs.size());
    std::vector<unsigned> entry_ids(sublogs.size());
    typename Sublogs::size_type i;
    unsigned new_entry_id;

    while (entry_ptr != nullptr)
    {
      i = entry_ptr->op().partition() % n;

      LogInfo<S>& log_info = sublogs[i];
      EntryPtr<S>& last_entry_ptr = last_entry_ptrs[i];

      if (log_info.log_head_ptr() == nullptr)
      {
        // initialize sub-log
        assert(entry_ptr->is_call());
        log_info.m_log_head_ptr = entry_ptr;
        log_info.m_number_of_entries = 1U;
      }
      else
      {
        // size of the sub-log increases
        ++log_info.m_number_of_entries;

        assert(last_entry_ptr != nullptr);
        last_entry_ptr->next = entry_ptr;
      }

      if (entry_ptr->is_call())
      {
        new_entry_id = entry_ids[i]++;
        entry_ptr->set_entry_id(new_entry_id);
        entry_ptr->match()->set_entry_id(new_entry_id);
      }

      next_entry_ptr = entry_ptr->next;
      entry_ptr->prev = last_entry_ptr;
      entry_ptr->next = nullptr;
      last_entry_ptr = entry_ptr;
      entry_ptr = next_entry_ptr;
    }
  }

  Sublogs m_sublogs;
  unsigned m_current_partition;

public:
  const Entry<S> log_head;
  const unsigned number_of_partitions;

  Slicer(LogInfo<S> log_info, unsigned _number_of_partitions)
  : m_sublogs(_number_of_partitions),
    m_current_partition{0U},
    log_head{log_info.log_head_ptr()},
    number_of_partitions{_number_of_partitions}
  {
    slice(log_head, m_sublogs);
  }

  const LogInfo<S>& sublog_info(unsigned partition) const
  {
    return m_sublogs[partition];
  }

  const LogInfo<S>& next_sublog_info()
  {
    static LogInfo<S> s_empty_log;

    unsigned partition = m_current_partition;
    ++m_current_partition;

    if (partition < number_of_partitions)
      return m_sublogs[partition];

    return s_empty_log;
  }
};

/// S - sequential data type
template<class S>
class ConcurrentLog
{
private:
  typedef std::vector<Entry<S>> Entries;
  typedef typename Entries::size_type Size;

  Entries m_entries;
  std::atomic<Size> m_index;

  static void link(EntryPtr<S> last_entry_ptr, Entry<S>& entry)
  {
    if (last_entry_ptr != nullptr)
      last_entry_ptr->next = &entry;

    entry.prev = last_entry_ptr;
  }

public:
  ConcurrentLog(Size capacity)
  : m_entries(capacity),
    m_index{0U} {}

  /// \remark thread-safe

  /// \pre: enough capacity
  EntryPtr<S> push_back(OpPtr<S>&& op_ptr)
  {
    // we use the relaxed memory order tag because we
    // do not need to read any other memory locations
    Size index = m_index.fetch_add(1U, std::memory_order_relaxed);

    assert(index < m_entries.size());

    // There is no data race, see [container.requirements.dataraces]
    // in Section 23.2.2, paragraph 2, p. 734 in the C++11 language
    // specification. Since the index was incremented atomically,
    // each thread accesses a different element in the vector.
    Entry<S>& entry = m_entries[index];
    entry.set_op(std::move(op_ptr));
    entry.set_thread_id(std::this_thread::get_id());

    return &entry;
  }

  /// \remark thread-safe

  /// \pre: enough capacity
  /// \post: call_entry_ptr->is_call()
  EntryPtr<S> push_back(EntryPtr<S> call_entry_ptr, OpPtr<S>&& op_ptr)
  {
    EntryPtr<S> entry_ptr = push_back(std::move(op_ptr));
    call_entry_ptr->set_match(entry_ptr);
    assert(call_entry_ptr->is_call());

    return entry_ptr;
  }

  /// \warning not thread-safe
  EntryPtr<S> log_head_ptr()
  {
    if (m_entries.front().next == nullptr)
    {
      unsigned entry_id{0U};
      Size index{0U};

      EntryPtr<S> last_entry_ptr{nullptr};
      for (Entry<S>& entry : m_entries)
      {
        if (index == m_index)
          break;

        ++index;

        if (entry.is_call())
        {
          entry.set_entry_id(entry_id);
          entry.match()->set_entry_id(entry_id);

          ++entry_id;
        }

        link(last_entry_ptr, entry);
        last_entry_ptr = &entry;
      }
    }

    return &m_entries.front();
  }

  /// \warning not thread-safe
  std::size_t number_of_entries() const noexcept
  {
    return m_index.load();
  }

  /// \warning not thread-safe
  LogInfo<S> info()
  {
    return {log_head_ptr(), number_of_entries()};
  }
};

/************* Models for sequential abstract data types *************/

class FlexibleBitset
{
public:
  typedef Bitset::Pos Pos;

private:
  Bitset m_bitset;

  void allocate_blocks_if_neccessary(Pos pos) noexcept
  {
    if (pos < Bitset::s_bits_per_block)
      return;

    assert(0U < pos);
    Bitset::BlockIndex new_size{Bitset::blocks_size(pos)};
    if (m_bitset.m_blocks.size() < new_size)
      m_bitset.m_blocks.resize(new_size);
  }

public:
  FlexibleBitset()
  : m_bitset{1U} {}

  FlexibleBitset(Pos max_pos)
  : m_bitset{max_pos} {}

  bool is_empty() const noexcept
  {
    return m_bitset.is_empty();
  }

  bool set(Pos pos)
  {
    allocate_blocks_if_neccessary(pos);
    return m_bitset.set(pos);
  }

  bool is_set(Pos pos) const
  {
    return m_bitset.is_set(pos);
  }

  bool reset(Pos pos)
  {
    allocate_blocks_if_neccessary(pos);
    return m_bitset.reset(pos);
  }

  /// Same size and bits?
  bool operator==(const FlexibleBitset& other) const noexcept
  {
    return m_bitset == other.m_bitset;
  }

  bool operator!=(const FlexibleBitset& other) const noexcept
  {
    return m_bitset != other.m_bitset;
  }

  std::size_t hash_code() const noexcept
  {
    return m_bitset.m_hash;
  }
};

namespace state
{
  namespace internal
  {
    template<class S, class Ret>
    struct RetOp : public Op<S>
    {
      typedef RetOp<S, Ret> Base;

      const Ret ret;

      RetOp(Ret r)
      : Op<S>(), ret{r} {}

#ifdef _LT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        return os << "ret: " << ret;
      }
#endif
    };

    template<class S, const char* const op_name>
    struct ZeroArgOp : public Op<S>
    {
      typedef ZeroArgOp<S, op_name> Base;

      ZeroArgOp()
      : Op<S>() {}

#ifdef _LT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        return os << op_name << "()";
      }
#endif
    };

    template<class S, class Value, const char* const op_name>
    struct ArgOp : public Op<S>
    {
      typedef ArgOp<S, Value, op_name> Base;

      const Value value;

      ArgOp(Value v)
      : Op<S>(v), value{v} {}

      ArgOp(bool is_partitionable, Value v)
      : Op<S>(is_partitionable, v), value{v} {}

#ifdef _LT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        return os << op_name << "(" << std::to_string(value) << ")";
      }
#endif
    };
  }

  /// Byte read-write register with CAS
  class Atomic
  {
  public:
    typedef signed char Value;

  private:
    static constexpr char s_read_op_name[] = "read";
    static constexpr char s_write_op_name[] = "write";

    struct ReadRetOp : public Op<Atomic>
    {
    private:
      const bool m_is_pending;
      const Value m_value;

    public:
      ReadRetOp(bool is_pending, Value value)
      : Op<Atomic>(),
        m_is_pending(is_pending),
        m_value{value} {}

      bool is_pending() const noexcept
      {
        return m_is_pending;
      }

      /// \pre: not is_pending()
      Value value() const
      {
        assert(not m_is_pending);
        return m_value;
      }

#ifdef _LT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        if (m_is_pending)
          return os << "read() : pending";

        return os << "read() : " << std::to_string(m_value);
      }
#endif
    };

    struct ReadCallOp : public internal::ZeroArgOp<Atomic, s_read_op_name>
    {
      ReadCallOp() : Base() {}

      std::pair<bool, Atomic> internal_apply(const Atomic& atomic, const Op<Atomic>& op) override
      {
        const ReadRetOp& read_ret = dynamic_cast<const ReadRetOp&>(op);

        if (read_ret.is_pending())
          return {true, atomic};

        return {atomic.get() == read_ret.value(), atomic};
      }
    };

    struct CASRetOp : public Op<Atomic>
    {
    private:
      // 0: pending, 1: failed, 2: ok
      const unsigned m_status;

    public:
      CASRetOp(unsigned status)
      : Op<Atomic>(),
        m_status(status) {}

      bool is_pending() const noexcept
      {
        return m_status == 0U;
      }

      /// \pre: not is_pending()
      bool is_ok() const
      {
        assert(0U < m_status);
        return m_status == 2U;
      }

#ifdef _LT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        os << "cas() : ";

        if (is_pending())
          return os << "pending";

        if (is_ok())
          return os << "succeeded";

        return os << "failed";
      }
#endif
    };

    struct CASCallOp : public Op<Atomic>
    {
      const Value current_value, new_value;

      CASCallOp(Value current_v, Value new_v)
      : Op<Atomic>(),
        current_value{current_v},
        new_value{new_v} {}

#ifdef _LT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        return os << "cas(" << std::to_string(current_value) << ", " << std::to_string(new_value) << ")";
      }
#endif

      std::pair<bool, Atomic> internal_apply(const Atomic& atomic, const Op<Atomic>& op) override
      {
        const CASRetOp& cas_ret = dynamic_cast<const CASRetOp&>(op);

        if (cas_ret.is_pending())
        {
          if (atomic.get() == current_value)
            return {true, atomic.set(new_value)};

          return {true, atomic};
        }

        if (atomic.get() == current_value)
          return {cas_ret.is_ok(), atomic.set(new_value)};

        return {not cas_ret.is_ok(), atomic};
      }
    };

    struct WriteRetOp : public Op<Atomic>
    {
      const bool is_pending;

      WriteRetOp(bool pending)
      : Op<Atomic>(),
        is_pending(pending) {}

#ifdef _LT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        if (is_pending)
          return os << "write() : pending";

        return os << "write() : succeeded";
      }
#endif
    };

    struct WriteCallOp : public internal::ArgOp<Atomic, Value, s_write_op_name>
    {
      typedef internal::ArgOp<Atomic, Value, s_write_op_name> Base;

      WriteCallOp(Value new_value)
      : Base(false, new_value) {}

      std::pair<bool, Atomic> internal_apply(const Atomic& atomic, const Op<Atomic>& op) override
      {
        const WriteRetOp& write_ret = dynamic_cast<const WriteRetOp&>(op);

        // we don't need to check write_ret.is_pending because if the
        // write is pending then it could be still linearized last
        return {true, atomic.set(Base::value)};
      }
    };

    Value m_value;

    Atomic(Value value) : m_value{value} {}

  public:
    typedef std::unique_ptr<Op<Atomic>> AtomicOpPtr;

    static AtomicOpPtr make_read_call()
    {
      return make_unique<ReadCallOp>();
    }

    static AtomicOpPtr make_read_ret(Value v)
    {
      return make_unique<ReadRetOp>(false, v);
    }

    static AtomicOpPtr make_read_pending()
    {
      return make_unique<ReadRetOp>(true, '\0');
    }

    static AtomicOpPtr make_write_call(Value v)
    {
      return make_unique<WriteCallOp>(v);
    }

    static AtomicOpPtr make_write_ret()
    {
      return make_unique<WriteRetOp>(false);
    }

    static AtomicOpPtr make_write_pending()
    {
      return make_unique<WriteRetOp>(true);
    }

    static AtomicOpPtr make_cas_call(Value curr_value, Value new_value)
    {
      return make_unique<CASCallOp>(curr_value, new_value);
    }

    static AtomicOpPtr make_cas_ret(bool ok)
    {
      return make_unique<CASRetOp>(1U + ok);
    }

    static AtomicOpPtr make_cas_pending()
    {
      return make_unique<CASRetOp>(0U);
    }

    /// Initially, register is negative
    Atomic() : m_value{-1} {}

    Value get() const noexcept
    {
      return m_value;
    }

    Atomic set(Value v) const noexcept
    {
      return {v};
    }

    bool operator==(const Atomic& atomic) const
    {
      return m_value == atomic.m_value;
    }

    bool operator!=(const Atomic& atomic) const
    {
      return m_value != atomic.m_value;
    }
  };

  constexpr char Atomic::s_read_op_name[];
  constexpr char Atomic::s_write_op_name[];

  template<>
  struct Hash<Atomic>
  {
    std::size_t operator()(const Atomic& atomic) const noexcept
    {
      return atomic.get() * 193U;
    }
  };

  class Set
  {
  public:
    typedef char Value;
    typedef bool Ret;

  private:
    static constexpr char s_empty_op_name[] = "empty";
    static constexpr char s_contains_op_name[] = "contains";
    static constexpr char s_insert_op_name[] = "insert";
    static constexpr char s_erase_op_name[] = "erase";

  public:
    struct RetOp : public internal::RetOp<Set, Ret>
    {
      RetOp(Ret r) : Base(r) {}
    };

    struct EmptyCallOp : public internal::ZeroArgOp<Set, s_empty_op_name>
    {
      EmptyCallOp() : Base() {}

      std::pair<bool, Set> internal_apply(const Set& set, const Op<Set>& op) override
      {
        const RetOp& empty_ret = dynamic_cast<const RetOp&>(op);
        bool ret = set.is_empty();
        return {ret == empty_ret.ret, set};
      }
    };

    struct ContainsCallOp : public internal::ArgOp<Set, Value, s_contains_op_name>
    {
      ContainsCallOp(Value v) : Base(v) {}

      std::pair<bool, Set> internal_apply(const Set& set, const Op<Set>& op) override
      {
        const RetOp& contains_ret = dynamic_cast<const RetOp&>(op);
        bool ret = set.contains(value);
        return {ret == contains_ret.ret, set};
      }
    };

    struct InsertCallOp : public internal::ArgOp<Set, Value, s_insert_op_name>
    {
      InsertCallOp(Value v) : Base(v) {}

      std::pair<bool, Set> internal_apply(const Set& set, const Op<Set>& op) override
      {
        bool ret;
        Set new_set;
        const RetOp& insert_ret = dynamic_cast<const RetOp&>(op);
        std::tie(ret, new_set) = set.insert(value);
        return {ret == insert_ret.ret, std::move(new_set)};
      }
    };

    struct EraseCallOp : public internal::ArgOp<Set, Value, s_erase_op_name>
    {
      EraseCallOp(Value v) : Base(v) {}

      std::pair<bool, Set> internal_apply(const Set& set, const Op<Set>& op) override
      {
        bool ret;
        Set new_set;
        const RetOp& erase_ret = dynamic_cast<const RetOp&>(op);
        std::tie(ret, new_set) = set.erase(value);
        return {ret == erase_ret.ret, std::move(new_set)};
      }
    };

    typedef std::unique_ptr<Op<Set>> SetOpPtr;
    FlexibleBitset m_bitset;

    Set(FlexibleBitset&& bitset)
    : m_bitset(std::move(bitset)) {}

  public:
    static SetOpPtr make_empty_call()
    {
      return make_unique<EmptyCallOp>();
    }

    static SetOpPtr make_contains_call(Value value)
    {
      return make_unique<ContainsCallOp>(value);
    }

    static SetOpPtr make_insert_call(Value value)
    {
      return make_unique<InsertCallOp>(value);
    }

    static SetOpPtr make_erase_call(Value value)
    {
      return make_unique<EraseCallOp>(value);
    }

    static SetOpPtr make_ret(Ret ret)
    {
      return make_unique<RetOp>(ret);
    }

    Set()
    : m_bitset{} {}

    const FlexibleBitset& bitset() const
    {
      return m_bitset;
    }

    bool is_empty() const
    {
      return m_bitset.is_empty();
    }

    bool contains(const Value& value) const
    {
      return m_bitset.is_set(value);
    }

    std::pair<bool, Set> insert(const Value& value) const
    {
      FlexibleBitset copy_bitset{m_bitset};
      bool ok = copy_bitset.set(value);
      return {ok, Set(std::move(copy_bitset))};
    }

    std::pair<bool, Set> erase(const Value& value) const
    {
      FlexibleBitset copy_bitset{m_bitset};
      bool ok = copy_bitset.reset(value);
      return {ok, Set(std::move(copy_bitset))};
    }

    bool operator==(const Set& set) const
    {
      return m_bitset == set.m_bitset;
    }

    bool operator!=(const Set& set) const
    {
      return m_bitset != set.m_bitset;
    }
  };

  constexpr char Set::s_empty_op_name[];
  constexpr char Set::s_contains_op_name[];
  constexpr char Set::s_insert_op_name[];
  constexpr char Set::s_erase_op_name[];

  template<>
  struct Hash<Set>
  {
    std::size_t operator()(const Set& set) const noexcept
    {
      return set.bitset().hash_code();
    }
  };

  /// Bounded stack

  /// N - stack capacity
  template<std::size_t N>
  class Stack
  {
  public:
    typedef char Value;

  private:
    static constexpr char s_try_push_op_name[] = "try_push";
    static constexpr char s_try_pop_op_name[] = "try_pop";

  public:
    struct TryPushCallOp : public internal::ArgOp<Stack<N>, Value, s_try_push_op_name>
    {
      typedef internal::ArgOp<Stack<N>, Value, s_try_push_op_name> Base;
      TryPushCallOp(Value v) : Base(v) {}

      std::pair<bool, Stack<N>> internal_apply(const Stack<N>& stack, const Op<Stack<N>>& op) override
      {
        typedef internal::RetOp<Stack<N>, bool> RetOp;

        const RetOp& try_push_ret = dynamic_cast<const RetOp&>(op);
        if (not stack.is_full())
          return {try_push_ret.ret, stack.push(Base::value)};

        return {not try_push_ret.ret, stack};
      }
    };

    struct TryPopRetOp : public Op<Stack<N>>
    {
    private:
      const Value m_value;

    public:
      TryPopRetOp(const std::pair<bool, Value>& pair)
      : Op<Stack<N>>(pair.first, pair.second),
        m_value{pair.second} {}

      bool ok() const
      {
        return Op<Stack<N>>::is_partitionable();
      }

      /// \pre: ok()
      Value value() const
      {
        assert(ok());
        return m_value;
      }

#ifdef _LT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        return os << "ret: [ok: " << ok() << ", value: " << (ok() ? std::to_string(value()) : "undefined") << "]";
      }
#endif
    };

    struct TryPopCallOp : public internal::ZeroArgOp<Stack<N>, s_try_pop_op_name>
    {
      typedef internal::ZeroArgOp<Stack<N>, s_try_pop_op_name> Base;
      TryPopCallOp() : Base() {}

      std::pair<bool, Stack<N>> internal_apply(const Stack<N>& stack, const Op<Stack<N>>& op) override
      {
        const TryPopRetOp& try_pop_ret = dynamic_cast<const TryPopRetOp&>(op);

        if (stack.is_empty())
          return {not try_pop_ret.ok(), stack};

        Value value{stack.top()};
        return {try_pop_ret.ok() and value == try_pop_ret.value(), stack.pop()};
      }
    };

    typedef std::unique_ptr<Op<Stack<N>>> StackOpPtr;

    class Node;
    typedef Node* NodePtr;

    /// Version tree of stacks
    class Node
    {
    private:
      friend class Stack<N>;

      // if m_prev is null, then m_size is zero
      const std::size_t m_size;

      // top of stack is defined if m_prev != nullptr
      const Value m_top;
      const NodePtr m_prev;
      unsigned m_ref_counter;

      std::vector<NodePtr> m_vector;

    public:
      ~Node()
      {
        if (m_prev == nullptr)
          return;

        m_prev->m_vector[m_top] = nullptr;
        if (--m_prev->m_ref_counter == 0)
          delete m_prev;
      }

      Node(const Node&) = delete;
      Node& operator=(const Node&) = delete;

      Node()
      : m_size{0},
        m_top{},
        m_prev{nullptr},
        m_ref_counter{0U},
        m_vector{} {}

      /// \pre: prev != nullptr
      Node(std::size_t size, Value value, const NodePtr& prev)
      : m_size{size},
        m_top{value},
        m_prev{prev},
        m_ref_counter{0U},
        m_vector{}
      {
        assert(prev != nullptr);
        ++prev->m_ref_counter;
      }

      /// Returns non-null pointer

      /// \pre: prev != nullptr
      NodePtr get_or_update_next(Value value, NodePtr& prev)
      {
        assert(prev != nullptr);

        if (m_vector.size() <= value)
          m_vector.resize(value + 1U);

        assert(value < m_vector.size());

        NodePtr& node_ptr = m_vector[value];
        if (node_ptr == nullptr)
          node_ptr = new Node(prev->size() + 1U, value, prev);

        assert(node_ptr != nullptr);
        assert(node_ptr->m_top == value);
        return node_ptr;
      }

      std::size_t size() const
      {
        assert(m_prev != nullptr or m_size == 0);
        return m_size;
      }

      const NodePtr& prev() const
      {
        return m_prev;
      }

      /// Defined if prev() != nullptr
      Value top() const noexcept
      {
        return m_top;
      }
    };

  public:
    static StackOpPtr make_try_push_call(Value value)
    {
      return make_unique<TryPushCallOp>(value);
    }

    static StackOpPtr make_try_push_ret(bool ok)
    {
      typedef internal::RetOp<Stack<N>, bool> RetOp;
      return make_unique<RetOp>(ok);
    }

    static StackOpPtr make_try_pop_call()
    {
      return make_unique<TryPopCallOp>();
    }

    static StackOpPtr make_try_pop_ret(bool ok, Value v)
    {
      return make_unique<TryPopRetOp>(std::make_pair(ok, v));
    }

   private:
    // never null, m_curr->size() <= N
    mutable NodePtr m_curr;

    void inc_ref_counter() const noexcept
    {
      if (m_curr != nullptr)
        ++m_curr->m_ref_counter;
    }

    void dec_ref_counter() const
    {
      assert(m_curr == nullptr or 0 < m_curr->m_ref_counter);

      if (m_curr != nullptr and --m_curr->m_ref_counter == 0)
        delete m_curr;
    }

    Stack(NodePtr curr)
    : m_curr{curr}
    {
      inc_ref_counter();
    }

   public:
    ~Stack()
    {
      dec_ref_counter();
    }

    Stack(const Stack& other)
    : m_curr{other.m_curr}
    {
      inc_ref_counter();
    }

    Stack(Stack&& other)
    : m_curr{other.m_curr}
    {
      other.m_curr = nullptr;
    }

    Stack& operator=(const Stack& other)
    {
      dec_ref_counter();
      m_curr = other.m_curr;
      inc_ref_counter();
      return *this;
    }

    Stack& operator=(Stack&& other)
    {
      dec_ref_counter();
      m_curr = other.m_curr;
      other.m_curr = nullptr;
      return *this;
    }

    Stack()
    : m_curr{new Node()}
    {
      inc_ref_counter();
    }

    bool is_empty() const
    {
      return m_curr->prev() == nullptr;
    }

    bool is_full() const
    {
      return m_curr->size() == N;
    }

    Stack<N> push(const Value& value) const
    {
      assert(not is_full());
      return {m_curr->get_or_update_next(value, m_curr)};
    }

    /// \pre: not is_empty()
    Stack<N> pop() const
    {
      assert(not is_empty());
      return {m_curr->prev()};
    }

    Value top() const
    {
      assert(not is_empty());
      return m_curr->top();
    }

    bool operator==(const Stack<N>& stack) const
    {
      return stack.m_curr == m_curr;
    }

    bool operator!=(const Stack<N>& stack) const
    {
      return stack.m_curr != m_curr;
    }

    std::size_t hash_code() const
    {
      // On many platforms (except systems with segmented addressing)
      // std::size_t is synonymous with std::uintptr_t.
      //
      // \see_also http://en.cppreference.com/w/cpp/types/size_t
      return reinterpret_cast<uintptr_t>(m_curr);
    }
  };

  template<std::size_t N>
  constexpr char Stack<N>::s_try_push_op_name[];

  template<std::size_t N>
  constexpr char Stack<N>::s_try_pop_op_name[];

  template<std::size_t N>
  struct Hash<Stack<N>>
  {
    std::size_t operator()(const Stack<N>& stack) const noexcept
    {
      return stack.hash_code();
    }
  };
}

/// Reads an etcd history collected with Jepsen and converts it to a Log
class JepsenEtcdParser
{
private:
  enum class EntryKind
  {
    INFO,
    INVOKE,
    OK,
    FAIL,
  };

  enum class Opname
  {
    READ,
    WRITE,
    CAS,
  };

  std::unordered_map<unsigned, EntryPtr<state::Atomic>> map;

  std::list<EntryPtr<state::Atomic>> timeout_read_calls;
  std::list<EntryPtr<state::Atomic>> timeout_write_calls;
  std::list<EntryPtr<state::Atomic>> timeout_cas_calls;

  std::string ignore;
  std::string process_string;
  unsigned process;
  std::string entry_kind_string;
  EntryKind entry_kind;
  std::string opname_string;
  Opname opname;
  std::string args;
  unsigned x, y;

public:
  Log<state::Atomic> log;

  JepsenEtcdParser() :
  map{},
  timeout_read_calls{},
  timeout_write_calls{},
  timeout_cas_calls{},
  log{1024} {}

  /// We want to extract lines of the following format:
  ///
  ///   INFO  jepsen.util - <process> \t <entry-kind> <op-name> <args>
  ///
  /// Example: INFO  jepsen.util - 3	:invoke	:read	nil\n
  void parse_line(std::string& line)
  {
    static std::string s_log_level = "INFO";
    static std::string s_jepsen_util = "jepsen.util";
    static std::string s_hyphen = "-";
    static std::string s_nil = "nil";
    static std::string s_info = ":info";
    static std::string s_invoke = ":invoke";
    static std::string s_ok = ":ok";
    static std::string s_read = ":read";
    static std::string s_write = ":write";
    static std::string s_cas = ":cas";
    static std::string s_timeout = ":timed-out";
    static std::string s_nemesis = ":nemesis";
    static std::string s_fail = ":fail";

    std::stringstream line_stream{line};

    line_stream >> ignore;
    if (ignore != s_log_level)
      return;

    line_stream >> ignore;
    if (ignore != s_jepsen_util)
      return;

    line_stream >> ignore;
    if (ignore != s_hyphen)
      return;

    line_stream >> process_string;
    if (process_string == s_nemesis)
      return;

    process = std::stoul(process_string);
    line_stream >> entry_kind_string;
    line_stream >> opname_string;
    line_stream >> args;

    if (entry_kind_string == s_info)
      entry_kind = EntryKind::INFO;
    else if (entry_kind_string == s_invoke)
      entry_kind = EntryKind::INVOKE;
    else if (entry_kind_string == s_ok)
      entry_kind = EntryKind::OK;
    else if (entry_kind_string == s_fail)
      entry_kind = EntryKind::FAIL;
    else
      throw std::runtime_error("Unexpected entry kind: " + entry_kind_string);

    if (opname_string == s_read)
      opname = Opname::READ;
    else if (opname_string == s_write)
      opname = Opname::WRITE;
    else if (opname_string == s_cas)
      opname = Opname::CAS;
    else
      throw std::runtime_error("Unexpected operator name: " + opname_string);

    if (args != s_timeout)
    {
      if (opname == Opname::CAS)
      {
        assert(args.front() == '[');
        assert(args.size() == 2);
        x = std::stoul(args.substr(1, args.size()));
        line_stream >> y;
      }
      else
      {
        if (args == s_nil)
          x = -1;
        else
          x = std::stoul(args);
      }
    }

    EntryPtr<state::Atomic> entry_ptr{nullptr};
    auto iter = map.find(process);
    if (iter == map.cend())
    {
      assert(entry_kind == EntryKind::INVOKE);
      switch (opname)
      {
      case Opname::READ:
        entry_ptr = log.add_call(state::Atomic::make_read_call());
        break;
      case Opname::WRITE:
        entry_ptr = log.add_call(state::Atomic::make_write_call(x));
        break;
      case Opname::CAS:
        entry_ptr = log.add_call(state::Atomic::make_cas_call(x, y));
        break;
      }

      map.emplace(process, entry_ptr);
    }
    else
    {
      assert(entry_kind == EntryKind::INFO or
             entry_kind == EntryKind::OK or
             entry_kind == EntryKind::FAIL);

      entry_ptr = iter->second;
      map.erase(iter);

      if (args == s_timeout)
      {
        assert(entry_kind == EntryKind::INFO);

        switch (opname)
        {
        case Opname::READ:
          timeout_read_calls.push_back(entry_ptr);
          break;
        case Opname::WRITE:
          timeout_write_calls.push_back(entry_ptr);
          break;
        case Opname::CAS:
          timeout_cas_calls.push_back(entry_ptr);
          break;
        }
      }
      else
      {
        assert(entry_kind == EntryKind::OK or entry_kind == EntryKind::FAIL);

        switch (opname)
        {
        case Opname::READ:
          log.add_ret(entry_ptr, state::Atomic::make_read_ret(x));
          break;
        case Opname::WRITE:
          log.add_ret(entry_ptr, state::Atomic::make_write_ret());
          break;
        case Opname::CAS:
          log.add_ret(entry_ptr, state::Atomic::make_cas_ret(entry_kind != EntryKind::FAIL));
          break;
        }
      }
    }
  }

  void parse(std::istream& istream)
  {
    std::string line;

    while (std::getline(istream, line))
      parse_line(line);

    for (EntryPtr<state::Atomic> entry_ptr : timeout_read_calls)
      log.add_ret(entry_ptr, state::Atomic::make_read_pending());

    for (EntryPtr<state::Atomic> entry_ptr : timeout_write_calls)
      log.add_ret(entry_ptr, state::Atomic::make_write_pending());

    for (EntryPtr<state::Atomic> entry_ptr : timeout_cas_calls)
      log.add_ret(entry_ptr, state::Atomic::make_cas_pending());
  }
};

}

/************* Unit tests and experiments *************/

using namespace lt;

static void test_lru_cache()
{
  LruCache<char> lru_cache{3};
  assert(lru_cache.insert('\1'));
  assert(not lru_cache.insert('\1'));

  assert(lru_cache.insert('\2'));
  assert(lru_cache.insert('\3'));
  assert(lru_cache.insert('\1'));
  assert(not lru_cache.insert('\3'));
  assert(lru_cache.insert('\4'));
  assert(lru_cache.insert('\1'));
}

static void test_atomic_op()
{
  bool ok;
  state::Atomic atomic, new_atomic;

  OpPtr<state::Atomic> read_call_op_ptr;

  OpPtr<state::Atomic> read_0_ret_op_ptr, read_0_pending_op_ptr;
  OpPtr<state::Atomic> read_1_ret_op_ptr;
  OpPtr<state::Atomic> read_2_ret_op_ptr;

  OpPtr<state::Atomic> write_1_call_op_ptr, write_1_ret_op_ptr, write_1_pending_op_ptr;
  OpPtr<state::Atomic> cas_2_succeeded_call_op_ptr, cas_2_succeeded_ret_op_ptr, cas_2_pending_op_ptr;
  OpPtr<state::Atomic> cas_2_failed_call_op_ptr, cas_2_failed_ret_op_ptr;

  read_call_op_ptr = state::Atomic::make_read_call();

  read_0_ret_op_ptr = state::Atomic::make_read_ret('\0');
  read_0_pending_op_ptr = state::Atomic::make_read_pending();
  read_1_ret_op_ptr = state::Atomic::make_read_ret('\1');
  read_2_ret_op_ptr = state::Atomic::make_read_ret('\2');

  write_1_call_op_ptr = state::Atomic::make_write_call('\1');
  write_1_ret_op_ptr = state::Atomic::make_write_ret();
  write_1_pending_op_ptr = state::Atomic::make_write_pending();

  cas_2_succeeded_call_op_ptr = state::Atomic::make_cas_call('\1', '\2');
  cas_2_succeeded_ret_op_ptr = state::Atomic::make_cas_ret(true);
  cas_2_pending_op_ptr = state::Atomic::make_cas_pending();

  cas_2_failed_call_op_ptr = state::Atomic::make_cas_call('\2', '\1');
  cas_2_failed_ret_op_ptr = state::Atomic::make_cas_ret(false);

  Op<state::Atomic>& read_call_op = *read_call_op_ptr;

  Op<state::Atomic>& read_0_ret_op = *read_0_ret_op_ptr;
  Op<state::Atomic>& read_0_pending_op = *read_0_pending_op_ptr;
  Op<state::Atomic>& read_1_ret_op = *read_1_ret_op_ptr;
  Op<state::Atomic>& read_2_ret_op = *read_2_ret_op_ptr;

  Op<state::Atomic>& write_1_call_op = *write_1_call_op_ptr;
  Op<state::Atomic>& write_1_ret_op = *write_1_ret_op_ptr;
  Op<state::Atomic>& write_1_pending_op = *write_1_pending_op_ptr;

  Op<state::Atomic>& cas_2_succeeded_call_op = *cas_2_succeeded_call_op_ptr;
  Op<state::Atomic>& cas_2_succeeded_ret_op = *cas_2_succeeded_ret_op_ptr;
  Op<state::Atomic>& cas_2_pending_op = *cas_2_pending_op_ptr;

  Op<state::Atomic>& cas_2_failed_call_op = *cas_2_failed_call_op_ptr;
  Op<state::Atomic>& cas_2_failed_ret_op = *cas_2_failed_ret_op_ptr;

  assert(not read_call_op.is_partitionable());
  assert(not read_0_ret_op.is_partitionable());
  assert(not read_0_pending_op.is_partitionable());
  assert(not read_1_ret_op.is_partitionable());
  assert(not read_2_ret_op.is_partitionable());

  assert(not write_1_call_op.is_partitionable());
  assert(not write_1_ret_op.is_partitionable());
  assert(not write_1_pending_op.is_partitionable());

  assert(not cas_2_succeeded_call_op.is_partitionable());
  assert(not cas_2_succeeded_ret_op.is_partitionable());
  assert(not cas_2_pending_op.is_partitionable());
  assert(not cas_2_failed_call_op.is_partitionable());
  assert(not cas_2_failed_ret_op.is_partitionable());

  std::tie(ok, new_atomic) = read_call_op.apply(atomic, read_0_ret_op);
  assert(atomic == new_atomic);
  assert(not ok);

  std::tie(ok, new_atomic) = read_call_op.apply(atomic, read_1_ret_op);
  assert(atomic == new_atomic);
  assert(not ok);

  std::tie(ok, new_atomic) = read_call_op.apply(atomic, read_0_pending_op);
  assert(atomic == new_atomic);
  assert(ok);

  std::tie(ok, new_atomic) = read_call_op.apply(atomic, read_1_ret_op);
  assert(atomic == new_atomic);
  assert(not ok);

  std::tie(ok, new_atomic) = write_1_call_op.apply(atomic, write_1_pending_op);
  assert(atomic != new_atomic);
  assert(ok);

  std::tie(ok, new_atomic) = write_1_call_op.apply(atomic, write_1_ret_op);
  assert(atomic != new_atomic);
  assert(ok);

  atomic = new_atomic;

  std::tie(ok, new_atomic) = read_call_op.apply(atomic, read_1_ret_op);
  assert(atomic == new_atomic);
  assert(ok);

  std::tie(ok, new_atomic) = read_call_op.apply(atomic, read_2_ret_op);
  assert(atomic == new_atomic);
  assert(not ok);

  std::tie(ok, new_atomic) = cas_2_failed_call_op.apply(atomic, cas_2_failed_ret_op);
  assert(atomic == new_atomic);
  assert(ok);

  std::tie(ok, new_atomic) = cas_2_failed_call_op.apply(atomic, cas_2_succeeded_ret_op);
  assert(atomic == new_atomic);
  assert(not ok);

  std::tie(ok, new_atomic) = cas_2_succeeded_call_op.apply(atomic, cas_2_pending_op);
  assert(atomic != new_atomic);
  assert(ok);

  std::tie(ok, new_atomic) = cas_2_succeeded_call_op.apply(atomic, cas_2_succeeded_ret_op);
  assert(atomic != new_atomic);
  assert(ok);

  atomic = new_atomic;

  std::tie(ok, new_atomic) = read_call_op.apply(atomic, read_2_ret_op);
  assert(atomic == new_atomic);
  assert(ok);
}

/// a few sanity checks
static void test_stack()
{
  Entry<state::Set> ret, call;
  call.set_op(state::Set::make_contains_call('\1'));
  ret.set_op(state::Set::make_ret(true));
  call.set_match(&ret);

  EntryPtr<state::Set> A{&call}, B{&call}, C{&call};

  Stack<state::Set> stack{3};

  assert(stack.is_empty());
  assert(not stack.is_full());
  assert(stack.size() == 0U);

  stack.push(A, state::Set());

  assert(std::get<0>(stack.top()) == A);
  assert(not stack.is_empty());
  assert(not stack.is_full());
  assert(stack.size() == 1U);

  stack.push(B, state::Set());

  assert(std::get<0>(stack.top()) == B);
  assert(not stack.is_empty());
  assert(not stack.is_full());
  assert(stack.size() == 2U);

  stack.push(C, state::Set());

  assert(std::get<0>(stack.top()) == C);
  assert(not stack.is_empty());
  assert(stack.is_full());
  assert(stack.size() == 3U);

  stack.pop();

  assert(std::get<0>(stack.top()) == B);
  assert(not stack.is_empty());
  assert(not stack.is_full());
  assert(stack.size() == 2U);

  stack.push(C, state::Set());

  assert(std::get<0>(stack.top()) == C);
  assert(not stack.is_empty());
  assert(stack.is_full());
  assert(stack.size() == 3U);

  // pop multiple entries at once
  stack.pop(2);

  assert(not stack.is_empty());
  assert(not stack.is_full());
  assert(stack.size() == 1U);

  stack.pop();

  assert(stack.is_empty());
  assert(not stack.is_full());
  assert(stack.size() == 0U);
}

static void test_bitset()
{
  constexpr unsigned N = 71;

  FlexibleBitset bitset;

  for (unsigned k{0U}; k < N; ++k)
    assert(not bitset.is_set(k));

  assert(bitset.is_empty());

  bitset.set(0);
  assert(bitset.is_set(0));
  assert(not bitset.is_empty());

  for (unsigned k{1U}; k < N; ++k)
    assert(not bitset.is_set(k));

  bitset.reset(0);
  assert(not bitset.is_set(0));
  assert(bitset.is_empty());

  bitset.set(1);
  assert(not bitset.is_set(0));
  assert(bitset.is_set(1));
  assert(not bitset.is_empty());

  for (unsigned k{2U}; k < N; ++k)
    assert(not bitset.is_set(k));

  bitset.set(70);
  assert(bitset.is_set(70));
  assert(not bitset.is_empty());

  for (unsigned k{2U}; k < N - 1U; ++k)
    assert(not bitset.is_set(k));

  FlexibleBitset another_bitset;
  another_bitset.set(1);
  another_bitset.set(70);

  FlexibleBitset yet_another_bitset(another_bitset);

  assert(bitset == another_bitset);
  assert(bitset == yet_another_bitset);

  constexpr unsigned bits_per_block = static_cast<unsigned>(sizeof(unsigned long) * CHAR_BIT);

  assert(not bitset.is_set(bits_per_block - 1U));
  assert(bitset.set(bits_per_block - 1U));
  assert(bitset.is_set(bits_per_block - 1U));

  assert(not bitset.is_set(bits_per_block));
  assert(bitset.set(bits_per_block));
  assert(bitset.is_set(bits_per_block));

  assert(not bitset.is_set(bits_per_block + 1U));
  assert(bitset.set(bits_per_block + 1U));
  assert(bitset.is_set(bits_per_block + 1U));

  assert(not bitset.is_set(2U * bits_per_block - 1U));
  assert(bitset.set(2U * bits_per_block - 1U));
  assert(bitset.is_set(2U * bits_per_block - 1U));

  assert(not bitset.is_set(2U * bits_per_block));
  assert(bitset.set(2U * bits_per_block));
  assert(bitset.is_set(2U * bits_per_block));

  assert(not bitset.is_set(2U * bits_per_block + 1U));
  assert(bitset.set(2U * bits_per_block + 1U));
  assert(bitset.is_set(2U * bits_per_block + 1U));

  bitset = another_bitset;

  assert(bitset.set(2U * bits_per_block - 1U));
  assert(bitset.reset(2U * bits_per_block - 1U));
  assert(bitset == another_bitset);

  assert(bitset.set(2U * bits_per_block));
  assert(bitset.reset(2U * bits_per_block));

  // different number of blocks
  assert(bitset != another_bitset);

  assert(bitset.set(2U * bits_per_block + 1U));
  assert(bitset.reset(2U * bits_per_block + 1U));

  // different number of blocks
  assert(bitset != another_bitset);
}

static void test_state_set()
{
  bool ok;
  state::Set set;

  assert(not set.contains('\1'));

  std::tie(ok, set) = set.insert('\1');
  assert(ok);

  assert(set.contains('\1'));

  // item is already in the set
  std::tie(ok, set) = set.insert('\1');
  assert(not ok);
  assert(set.contains('\1'));

  std::tie(ok, set) = set.erase('\1');
  assert(ok);
  assert(not set.contains('\1'));

  // item has been already erased from the set
  std::tie(ok, set) = set.erase('\1');
  assert(not ok);
  assert(not set.contains('\1'));
}

static void test_state_set_op()
{
  bool ok;
  state::Set set, new_set;

  OpPtr<state::Set> empty_op_ptr;
  OpPtr<state::Set> contains_op_ptr;
  OpPtr<state::Set> insert_op_ptr;
  OpPtr<state::Set> erase_op_ptr;

  OpPtr<state::Set> true_ret_op_ptr{state::Set::make_ret(true)};
  OpPtr<state::Set> false_ret_op_ptr{state::Set::make_ret(false)};

  const Op<state::Set>& true_ret_op = *true_ret_op_ptr;
  const Op<state::Set>& false_ret_op = *false_ret_op_ptr;

  empty_op_ptr = state::Set::make_empty_call();
  contains_op_ptr = state::Set::make_contains_call('\1');
  insert_op_ptr = state::Set::make_insert_call('\1');
  erase_op_ptr = state::Set::make_erase_call('\1');

  Op<state::Set>& empty_op = *empty_op_ptr;
  Op<state::Set>& contains_op = *contains_op_ptr;
  Op<state::Set>& insert_op = *insert_op_ptr;
  Op<state::Set>& erase_op = *erase_op_ptr;

  std::tie(ok, new_set) = empty_op.apply(set, true_ret_op);
  assert(set == new_set);
  assert(ok);

  std::tie(ok, new_set) = contains_op.apply(set, false_ret_op);
  assert(set == new_set);
  assert(ok);

  std::tie(ok, new_set) = insert_op.apply(set, true_ret_op);
  assert(set != new_set);
  assert(ok);

  set = new_set;

  std::tie(ok, new_set) = empty_op.apply(set, false_ret_op);
  assert(set == new_set);
  assert(ok);

  std::tie(ok, new_set) = contains_op.apply(set, true_ret_op);
  assert(set == new_set);
  assert(ok);

  // item is already in the set, so insertion is unsuccessful
  std::tie(ok, new_set) = insert_op.apply(set, false_ret_op);
  assert(set == new_set);
  assert(ok);

  std::tie(ok, new_set) = contains_op.apply(set, true_ret_op);
  assert(set == new_set);
  assert(ok);

  std::tie(ok, new_set) = erase_op.apply(set, true_ret_op);
  assert(set != new_set);
  assert(ok);

  assert(std::get<0>(contains_op.apply(set, true_ret_op)));
  assert(not std::get<0>(contains_op.apply(set, false_ret_op)));

  assert(not std::get<0>(contains_op.apply(new_set, true_ret_op)));
  assert(std::get<0>(contains_op.apply(new_set, false_ret_op)));
}

static void test_state_stack()
{
  constexpr unsigned N = 2;

  state::Stack<N> stack;
  state::Stack<N> new_stack;
  state::Stack<N> stack_1, stack_2;

  assert(stack.is_empty());
  assert(not stack.is_full());

  new_stack = stack.push('\1');

  assert(stack != new_stack);
  stack = stack_1 = new_stack;

  assert(not stack.is_empty());
  assert(not stack.is_full());

  assert(stack.top() == '\1');

  new_stack = stack.push('\2');

  assert(stack != new_stack);
  stack = stack_2 = new_stack;

  assert(stack_1 != stack_2);

  assert(not stack.is_empty());
  assert(stack.is_full());

  assert(stack.top() == '\2');

  new_stack = stack.pop();
  assert(new_stack == stack_1);

  stack = new_stack;

  assert(not stack.is_empty());
  assert(not stack.is_full());

  assert(stack.top() == '\1');

  new_stack = stack.push('\2');

  assert(stack != new_stack);
  assert(new_stack == stack_2);

  stack = new_stack;

  assert(not stack.is_empty());
  assert(stack.is_full());

  assert(stack.top() == '\2');

  new_stack = stack.pop();
  assert(new_stack == stack_1);

  stack = new_stack;

  assert(not stack.is_empty());
  assert(not stack.is_full());

  assert(stack.top() == '\1');

  new_stack = stack.push('\3');

  assert(stack != new_stack);
  assert(new_stack != stack_1);
  assert(new_stack != stack_2);

  stack = new_stack;

  assert(not stack.is_empty());
  assert(stack.is_full());

  assert(stack.top() == '\3');
}

static void test_state_stack_op()
{
  constexpr unsigned N = 1;

  bool ok;
  state::Stack<N> stack, new_stack;

  OpPtr<state::Stack<N>> try_push_1_op_ptr, try_push_2_op_ptr;
  OpPtr<state::Stack<N>> try_pop_op_ptr;

  OpPtr<state::Stack<N>> true_try_push_ret_op_ptr{state::Stack<N>::make_try_push_ret(true)};
  OpPtr<state::Stack<N>> false_try_push_ret_op_ptr{state::Stack<N>::make_try_push_ret(false)};

  const Op<state::Stack<N>>& true_try_push_ret_op = *true_try_push_ret_op_ptr;
  const Op<state::Stack<N>>& false_try_push_ret_op = *false_try_push_ret_op_ptr;

  OpPtr<state::Stack<N>> true_1_try_pop_ret_op_ptr{state::Stack<N>::make_try_pop_ret(true, '\1')};
  OpPtr<state::Stack<N>> true_2_try_pop_ret_op_ptr{state::Stack<N>::make_try_pop_ret(true, '\2')};
  OpPtr<state::Stack<N>> false_try_pop_ret_op_ptr{state::Stack<N>::make_try_pop_ret(false, '\0')};

  const Op<state::Stack<N>>& true_1_try_pop_ret_op = *true_1_try_pop_ret_op_ptr;
  const Op<state::Stack<N>>& true_2_try_pop_ret_op = *true_2_try_pop_ret_op_ptr;
  const Op<state::Stack<N>>& false_try_pop_ret_op = *false_try_pop_ret_op_ptr;

  try_pop_op_ptr = state::Stack<N>::make_try_pop_call();
  Op<state::Stack<N>>& try_pop_op = *try_pop_op_ptr;

  std::tie(ok, new_stack) = try_pop_op.apply(stack, false_try_pop_ret_op);
  assert(stack == new_stack);
  assert(ok);

  std::tie(ok, new_stack) = try_pop_op.apply(stack, true_1_try_pop_ret_op);
  assert(stack == new_stack);
  assert(not ok);

  std::tie(ok, new_stack) = try_pop_op.apply(stack, true_2_try_pop_ret_op);
  assert(stack == new_stack);
  assert(not ok);

  try_push_2_op_ptr = state::Stack<N>::make_try_push_call('\2');
  Op<state::Stack<N>>& try_push_2_op = *try_push_2_op_ptr;

  std::tie(ok, new_stack) = try_push_2_op.apply(stack, false_try_push_ret_op);
  assert(stack != new_stack);
  assert(not ok);

  std::tie(ok, new_stack) = try_push_2_op.apply(stack, true_try_push_ret_op);
  assert(stack != new_stack);
  assert(ok);

  stack = new_stack;

  try_push_1_op_ptr = state::Stack<N>::make_try_push_call('\1');
  Op<state::Stack<N>>& try_push_1_op = *try_push_1_op_ptr;

  // stack is full
  std::tie(ok, new_stack) = try_push_1_op.apply(stack, false_try_push_ret_op);
  assert(stack == new_stack);
  assert(ok);

  std::tie(ok, new_stack) = try_push_1_op.apply(stack, true_try_push_ret_op);
  assert(stack == new_stack);
  assert(not ok);

  std::tie(ok, new_stack) = try_pop_op.apply(stack, false_try_pop_ret_op);
  assert(stack != new_stack);
  assert(not ok);

  std::tie(ok, new_stack) = try_pop_op.apply(stack, true_1_try_pop_ret_op);
  assert(stack != new_stack);
  assert(not ok);

  std::tie(ok, new_stack) = try_pop_op.apply(stack, true_2_try_pop_ret_op);
  assert(stack != new_stack);
  assert(ok);
}

/// The empty log is trivially linearizable.
static void test_linearizability_empty_log()
{
  std::size_t number_of_entries{0U};
  LogInfo<state::Set> log_info;
  LinearizabilityTester<state::Set> t{log_info};
  assert(log_info.is_empty());
  assert(t.check());
}

/// a few sanity checks on the raw entry data structure
static void test_raw_single_contains_is_linearizable()
{
  Entry<state::Set> contains_call, contains_ret;

  contains_ret.set_op(state::Set::make_ret(false));
  contains_ret.prev = &contains_call;

  contains_call.set_op(state::Set::make_contains_call('\1'));
  contains_call.next = &contains_ret;
  contains_call.set_match(&contains_ret);

  std::size_t number_of_entries{2U};
  LogInfo<state::Set> log_info{&contains_call, number_of_entries};
  LinearizabilityTester<state::Set> t{log_info};
  assert(t.check());
}

static void test_raw_single_contains_is_not_linearizable()
{
  Entry<state::Set> contains_call, contains_ret;

  contains_ret.set_op(state::Set::make_ret(true));
  contains_ret.prev = &contains_call;

  contains_call.set_op(state::Set::make_contains_call('\1'));
  contains_call.next = &contains_ret;
  contains_call.set_match(&contains_ret);

  std::size_t number_of_entries{2U};
  LogInfo<state::Set> log_info{&contains_call, number_of_entries};
  LinearizabilityTester<state::Set> t{log_info};
  assert(not t.check());
}

static void test_single_contains(bool ret)
{
  Log<state::Set> log{4U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;

  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call('\1'));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(ret));

  assert(log.log_head_ptr() == contains_call_entry_ptr);
  assert(log.number_of_entries() == 2U);

  assert(log.log_head_ptr() == contains_call_entry_ptr);
  assert(contains_call_entry_ptr->prev == nullptr);
  assert(contains_call_entry_ptr->next == contains_ret_entry_ptr);
  assert(contains_call_entry_ptr->match() == contains_ret_entry_ptr);

  assert(contains_ret_entry_ptr->match() == contains_call_entry_ptr);
  assert(contains_ret_entry_ptr->prev == contains_call_entry_ptr);
  assert(contains_ret_entry_ptr->next == nullptr);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == (not ret));

  if (ret)
  {
    // If log cannot be linearized, then all pointers
    // (except the first one) are still the same.
    assert(log.log_head_ptr() == contains_call_entry_ptr);
    assert(contains_call_entry_ptr->prev != nullptr);
    assert(contains_call_entry_ptr->next == contains_ret_entry_ptr);
    assert(contains_call_entry_ptr->match() == contains_ret_entry_ptr);

    assert(contains_ret_entry_ptr->match() == contains_call_entry_ptr);
    assert(contains_ret_entry_ptr->prev == contains_call_entry_ptr);
    assert(contains_ret_entry_ptr->next == nullptr);
  }
}

static void test_log_copy()
{
  constexpr bool ret = true;

  Log<state::Set> log{4U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;

  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call('\1'));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(ret));

  assert(log.log_head_ptr() == contains_call_entry_ptr);
  assert(log.number_of_entries() == 2U);

  assert(log.log_head_ptr() == contains_call_entry_ptr);
  assert(contains_call_entry_ptr->prev == nullptr);
  assert(contains_call_entry_ptr->next == contains_ret_entry_ptr);
  assert(contains_call_entry_ptr->match() == contains_ret_entry_ptr);

  assert(contains_ret_entry_ptr->match() == contains_call_entry_ptr);
  assert(contains_ret_entry_ptr->prev == contains_call_entry_ptr);
  assert(contains_ret_entry_ptr->next == nullptr);

  Log<state::Set> log_copy{log.info()};

  assert(log_copy.log_head_ptr() != contains_call_entry_ptr);
  assert(log_copy.log_head_ptr() != contains_call_entry_ptr);
  assert(log_copy.log_head_ptr()->entry_id() == 0U);
  assert(&log_copy.log_head_ptr()->op() == &contains_call_entry_ptr->op());
  assert(log_copy.log_head_ptr() == log_copy.log_head_ptr()->match()->match());
  assert(log_copy.log_head_ptr()->prev == nullptr);
  assert(log_copy.number_of_entries() == 2U);
}

//   contains(x) : contains_ret
// |---------------------------|
//
//         insert(x) : insert_ret
//     |---------------------------|
static void test_000(bool insert_ret, bool contains_ret)
{
  constexpr char x = '\1';

  constexpr unsigned contains_entry_id{0U};
  constexpr unsigned insert_entry_id{1U};

  Log<state::Set> log{4U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;
  EntryPtr<state::Set> insert_call_entry_ptr, insert_ret_entry_ptr;

  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  insert_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(contains_ret));
  insert_ret_entry_ptr = log.add_ret(insert_call_entry_ptr, state::Set::make_ret(insert_ret));

  assert(insert_call_entry_ptr->entry_id() == insert_entry_id);
  assert(insert_ret_entry_ptr->entry_id() == insert_entry_id);

  assert(contains_call_entry_ptr->entry_id() == contains_entry_id);
  assert(contains_ret_entry_ptr->entry_id() == contains_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == insert_ret);
}

//        contains(x) : contains_ret
//      |----------------------------|
//
//    insert(x) : insert_ret
// |-------------------------|
static void test_001(bool insert_ret, bool contains_ret)
{
  constexpr char x = '\1';

  constexpr unsigned insert_entry_id{0U};
  constexpr unsigned contains_entry_id{1U};

  Log<state::Set> log{4U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;
  EntryPtr<state::Set> insert_call_entry_ptr, insert_ret_entry_ptr;

  insert_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  insert_ret_entry_ptr = log.add_ret(insert_call_entry_ptr, state::Set::make_ret(insert_ret));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(contains_ret));

  assert(insert_call_entry_ptr->entry_id() == insert_entry_id);
  assert(insert_ret_entry_ptr->entry_id() == insert_entry_id);

  assert(contains_call_entry_ptr->entry_id() == contains_entry_id);
  assert(contains_ret_entry_ptr->entry_id() == contains_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == insert_ret);
}

//      contains(x) : contains_ret
//    |----------------------------|
//
//       insert(x) : insert_ret
// |----------------------------------|
static void test_002(bool insert_ret, bool contains_ret)
{
  constexpr char x = '\1';

  constexpr unsigned insert_entry_id{0U};
  constexpr unsigned contains_entry_id{1U};

  Log<state::Set> log{4U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;
  EntryPtr<state::Set> insert_call_entry_ptr, insert_ret_entry_ptr;

  insert_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(contains_ret));
  insert_ret_entry_ptr = log.add_ret(insert_call_entry_ptr, state::Set::make_ret(insert_ret));

  assert(insert_call_entry_ptr->entry_id() == insert_entry_id);
  assert(insert_ret_entry_ptr->entry_id() == insert_entry_id);

  assert(contains_call_entry_ptr->entry_id() == contains_entry_id);
  assert(contains_ret_entry_ptr->entry_id() == contains_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == insert_ret);
}

//     contains(x) : contains_ret
// |----------------------------------|
//
//       insert(x) : insert_ret
//    |---------------------------|
static void test_003(bool insert_ret, bool contains_ret)
{
  constexpr char x = '\1';

  constexpr unsigned contains_entry_id{0U};
  constexpr unsigned insert_entry_id{1U};

  Log<state::Set> log{4U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;
  EntryPtr<state::Set> insert_call_entry_ptr, insert_ret_entry_ptr;

  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  insert_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_ret_entry_ptr = log.add_ret(insert_call_entry_ptr, state::Set::make_ret(insert_ret));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(contains_ret));

  assert(insert_call_entry_ptr->entry_id() == insert_entry_id);
  assert(insert_ret_entry_ptr->entry_id() == insert_entry_id);

  assert(contains_call_entry_ptr->entry_id() == contains_entry_id);
  assert(contains_ret_entry_ptr->entry_id() == contains_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == insert_ret);
}

//   insert(x) : insert_ret     contains(x) : contains_ret
// |------------------------| |---------------------------|
static void test_004(bool insert_ret, bool contains_ret)
{
  constexpr char x = '\1';

  constexpr unsigned insert_entry_id{0U};
  constexpr unsigned contains_entry_id{1U};

  Log<state::Set> log{4U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;
  EntryPtr<state::Set> insert_call_entry_ptr, insert_ret_entry_ptr;

  insert_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_ret_entry_ptr = log.add_ret(insert_call_entry_ptr, state::Set::make_ret(insert_ret));
  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(contains_ret));

  assert(insert_call_entry_ptr->entry_id() == insert_entry_id);
  assert(insert_ret_entry_ptr->entry_id() == insert_entry_id);

  assert(contains_call_entry_ptr->entry_id() == contains_entry_id);
  assert(contains_ret_entry_ptr->entry_id() == contains_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == (insert_ret and contains_ret));
}

//   contains(x) : contains_ret    insert(x) : insert_ret
// |---------------------------| |------------------------| 
static void test_005(bool insert_ret, bool contains_ret)
{
  constexpr char x = '\1';

  constexpr unsigned contains_entry_id{0U};
  constexpr unsigned insert_entry_id{1U};

  Log<state::Set> log{4U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;
  EntryPtr<state::Set> insert_call_entry_ptr, insert_ret_entry_ptr;

  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(contains_ret));
  insert_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_ret_entry_ptr = log.add_ret(insert_call_entry_ptr, state::Set::make_ret(insert_ret));

  assert(insert_call_entry_ptr->entry_id() == insert_entry_id);
  assert(insert_ret_entry_ptr->entry_id() == insert_entry_id);

  assert(contains_call_entry_ptr->entry_id() == contains_entry_id);
  assert(contains_ret_entry_ptr->entry_id() == contains_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == (insert_ret and not contains_ret));
}

//   insert(x) : insert_ret_0
// |--------------------------|
//
//       insert(x) : insert_ret_1
//     |--------------------------|
static void test_006(bool insert_ret_0, bool insert_ret_1)
{
  constexpr char x = '\1';

  constexpr unsigned insert_0_entry_id{0U};
  constexpr unsigned insert_1_entry_id{1U};

  EntryPtr<state::Set> insert_call_0_entry_ptr, insert_ret_0_entry_ptr;
  EntryPtr<state::Set> insert_call_1_entry_ptr, insert_ret_1_entry_ptr;

  Log<state::Set> log{4U};

  insert_call_0_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_call_1_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_ret_0_entry_ptr = log.add_ret(insert_call_0_entry_ptr, state::Set::make_ret(insert_ret_0));
  insert_ret_1_entry_ptr = log.add_ret(insert_call_1_entry_ptr, state::Set::make_ret(insert_ret_1));

  assert(insert_call_0_entry_ptr->entry_id() == insert_0_entry_id);
  assert(insert_ret_0_entry_ptr->entry_id() == insert_0_entry_id);

  assert(insert_call_1_entry_ptr->entry_id() == insert_1_entry_id);
  assert(insert_ret_1_entry_ptr->entry_id() == insert_1_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == (not (insert_ret_0 == insert_ret_1)));
}

//   insert(x) : insert_ret_0     insert(x) : insert_ret_1
// |--------------------------| |--------------------------|
static void test_007(bool insert_ret_0, bool insert_ret_1)
{
  constexpr char x = '\1';

  constexpr unsigned insert_0_entry_id{0U};
  constexpr unsigned insert_1_entry_id{1U};

  EntryPtr<state::Set> insert_call_0_entry_ptr, insert_ret_0_entry_ptr;
  EntryPtr<state::Set> insert_call_1_entry_ptr, insert_ret_1_entry_ptr;

  Log<state::Set> log{4U};

  insert_call_0_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_ret_0_entry_ptr = log.add_ret(insert_call_0_entry_ptr, state::Set::make_ret(insert_ret_0));
  insert_call_1_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_ret_1_entry_ptr = log.add_ret(insert_call_1_entry_ptr, state::Set::make_ret(insert_ret_1));

  assert(insert_call_0_entry_ptr->entry_id() == insert_0_entry_id);
  assert(insert_ret_0_entry_ptr->entry_id() == insert_0_entry_id);

  assert(insert_call_1_entry_ptr->entry_id() == insert_1_entry_id);
  assert(insert_ret_1_entry_ptr->entry_id() == insert_1_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == (insert_ret_0 and not insert_ret_1));
}

//           insert(x) : insert_ret
// |------------------------------------------|
//
//           insert(x) : insert_ret
//   |-------------------------------------|
//
//         contains(x) : contains_ret
//       |----------------------------|
//
static void test_008(bool insert_ret, bool contains_ret)
{
  constexpr char x = '\1';

  constexpr unsigned insert_0_entry_id{0U};
  constexpr unsigned insert_1_entry_id{1U};
  constexpr unsigned contains_entry_id{2U};

  Log<state::Set> log{8U};
  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;
  EntryPtr<state::Set> insert_0_call_entry_ptr, insert_0_ret_entry_ptr;
  EntryPtr<state::Set> insert_1_call_entry_ptr, insert_1_ret_entry_ptr;

  insert_0_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_1_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(contains_ret));
  insert_1_ret_entry_ptr = log.add_ret(insert_1_call_entry_ptr, state::Set::make_ret(insert_ret));
  insert_0_ret_entry_ptr = log.add_ret(insert_0_call_entry_ptr, state::Set::make_ret(insert_ret));

  assert(insert_0_call_entry_ptr->entry_id() == insert_0_entry_id);
  assert(insert_0_ret_entry_ptr->entry_id() == insert_0_entry_id);

  assert(insert_1_call_entry_ptr->entry_id() == insert_1_entry_id);
  assert(insert_1_ret_entry_ptr->entry_id() == insert_1_entry_id);

  assert(contains_call_entry_ptr->entry_id() == contains_entry_id);
  assert(contains_ret_entry_ptr->entry_id() == contains_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

// Not linearizable:
//
// Let x and y be distinct values.
//
//   contains(x) : false 
// |---------------------|
//
//      contains(y) : false
//    |---------------------|
//
//          insert(x) : false
//        |---------------------|
static void test_009()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  constexpr unsigned contains_x_entry_id{0U};
  constexpr unsigned contains_y_entry_id{1U};
  constexpr unsigned insert_x_entry_id{2U};

  Log<state::Set> log{6U};

  EntryPtr<state::Set> contains_x_call_entry_ptr, contains_x_ret_entry_ptr;
  EntryPtr<state::Set> contains_y_call_entry_ptr, contains_y_ret_entry_ptr;
  EntryPtr<state::Set> insert_x_call_entry_ptr, insert_x_ret_entry_ptr;

  contains_x_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_y_call_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  insert_x_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));

  contains_x_ret_entry_ptr = log.add_ret(contains_x_call_entry_ptr, state::Set::make_ret(false));
  contains_y_ret_entry_ptr = log.add_ret(contains_y_call_entry_ptr, state::Set::make_ret(false));
  insert_x_ret_entry_ptr = log.add_ret(insert_x_call_entry_ptr, state::Set::make_ret(false));

  assert(contains_x_call_entry_ptr->entry_id() == contains_x_entry_id);
  assert(contains_x_ret_entry_ptr->entry_id() == contains_x_entry_id);

  assert(contains_y_call_entry_ptr->entry_id() == contains_y_entry_id);
  assert(contains_y_ret_entry_ptr->entry_id() == contains_y_entry_id);

  assert(insert_x_call_entry_ptr->entry_id() == insert_x_entry_id);
  assert(insert_x_ret_entry_ptr->entry_id() == insert_x_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

// Not linearizable:
//
// Let x and y be distinct values.
//
//   contains(x) : false 
// |---------------------|
//
//       insert(x) : false
//    |---------------------|
//
//          contains(y) : false
//        |---------------------|
static void test_010()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  constexpr unsigned contains_x_entry_id{0U};
  constexpr unsigned insert_x_entry_id{1U};
  constexpr unsigned contains_y_entry_id{2U};

  Log<state::Set> log{6U};

  EntryPtr<state::Set> contains_x_call_entry_ptr, contains_x_ret_entry_ptr;
  EntryPtr<state::Set> contains_y_call_entry_ptr, contains_y_ret_entry_ptr;
  EntryPtr<state::Set> insert_x_call_entry_ptr, insert_x_ret_entry_ptr;

  contains_x_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  insert_x_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  contains_y_call_entry_ptr = log.add_call(state::Set::make_contains_call(y));

  contains_x_ret_entry_ptr = log.add_ret(contains_x_call_entry_ptr, state::Set::make_ret(false));
  insert_x_ret_entry_ptr = log.add_ret(insert_x_call_entry_ptr, state::Set::make_ret(false));
  contains_y_ret_entry_ptr = log.add_ret(contains_y_call_entry_ptr, state::Set::make_ret(false));

  assert(contains_x_call_entry_ptr->entry_id() == contains_x_entry_id);
  assert(contains_x_ret_entry_ptr->entry_id() == contains_x_entry_id);

  assert(insert_x_call_entry_ptr->entry_id() == insert_x_entry_id);
  assert(insert_x_ret_entry_ptr->entry_id() == insert_x_entry_id);

  assert(contains_y_call_entry_ptr->entry_id() == contains_y_entry_id);
  assert(contains_y_ret_entry_ptr->entry_id() == contains_y_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

// Linearizable:
//
// Let x and y be distinct values.
//
//   insert(x) : true
// |------------------|
//
//      contains(y) : false
//    |---------------------|
//
//         contains(x) : false
//       |---------------------|
static void test_011()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  constexpr unsigned insert_x_entry_id{0U};
  constexpr unsigned contains_y_entry_id{1U};
  constexpr unsigned contains_x_entry_id{2U};

  Log<state::Set> log{6U};

  EntryPtr<state::Set> insert_x_call_entry_ptr, insert_x_ret_entry_ptr;
  EntryPtr<state::Set> contains_y_call_entry_ptr, contains_y_ret_entry_ptr;
  EntryPtr<state::Set> contains_x_call_entry_ptr, contains_x_ret_entry_ptr;

  insert_x_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  contains_y_call_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  contains_x_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));

  insert_x_ret_entry_ptr = log.add_ret(insert_x_call_entry_ptr, state::Set::make_ret(true));
  contains_y_ret_entry_ptr = log.add_ret(contains_y_call_entry_ptr, state::Set::make_ret(false));
  contains_x_ret_entry_ptr = log.add_ret(contains_x_call_entry_ptr, state::Set::make_ret(false));

  assert(insert_x_call_entry_ptr->entry_id() == insert_x_entry_id);
  assert(insert_x_ret_entry_ptr->entry_id() == insert_x_entry_id);

  assert(contains_y_call_entry_ptr->entry_id() == contains_y_entry_id);
  assert(contains_y_ret_entry_ptr->entry_id() == contains_y_entry_id);

  assert(contains_x_call_entry_ptr->entry_id() == contains_x_entry_id);
  assert(contains_x_ret_entry_ptr->entry_id() == contains_x_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check());
}

// Linearizable:
//
// Let x and y be distinct values.
//
//   erase(x) : false     insert(y) : true
// |------------------| |------------------|
//
//                                               contains(x) : true
//                                 |------------------------------------------------|
//
//                                      contains(y) : false     insert(x) : true
//                                    |---------------------| |------------------|
static void test_012()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  Log<state::Set> log{10U};

  EntryPtr<state::Set> erase_x_call_entry_ptr, erase_x_ret_entry_ptr;
  EntryPtr<state::Set> insert_x_call_entry_ptr, insert_x_ret_entry_ptr;
  EntryPtr<state::Set> contains_x_call_entry_ptr, contains_x_ret_entry_ptr;
  EntryPtr<state::Set> insert_y_call_entry_ptr, insert_y_ret_entry_ptr;
  EntryPtr<state::Set> contains_y_call_entry_ptr, contains_y_ret_entry_ptr;

  erase_x_call_entry_ptr = log.add_call(state::Set::make_erase_call(x));
  erase_x_ret_entry_ptr = log.add_ret(erase_x_call_entry_ptr, state::Set::make_ret(false));
  insert_y_call_entry_ptr = log.add_call(state::Set::make_insert_call(y));
  contains_x_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_y_call_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  insert_y_ret_entry_ptr = log.add_ret(insert_y_call_entry_ptr, state::Set::make_ret(true));
  contains_y_ret_entry_ptr = log.add_ret(contains_y_call_entry_ptr, state::Set::make_ret(false));
  insert_x_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_x_ret_entry_ptr = log.add_ret(insert_x_call_entry_ptr, state::Set::make_ret(true));
  contains_x_ret_entry_ptr = log.add_ret(contains_x_call_entry_ptr, state::Set::make_ret(true));

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check());
}

// entry id: X0, call: contains(x)
// entry id: X1, call: insert(x)
// entry id: X0, return: ret: 0
// entry id: X2, call: contains(x)
// entry id: X2, return: ret: 0
// entry id: X3, call: insert(x)
// entry id: X3, return: ret: 1
// entry id: X4, call: contains(x)
// entry id: X4, return: ret: 1
// entry id: X1, return: ret: 0
// entry id: X5, call: contains(x)
// entry id: X5, return: ret: 1
static void test_013()
{
  constexpr char x = '\1';

  Log<state::Set> log{12U};

  EntryPtr<state::Set> call_x0_entry_ptr, ret_x0_entry_ptr;
  EntryPtr<state::Set> call_x1_entry_ptr, ret_x1_entry_ptr;
  EntryPtr<state::Set> call_x2_entry_ptr, ret_x2_entry_ptr;
  EntryPtr<state::Set> call_x3_entry_ptr, ret_x3_entry_ptr;
  EntryPtr<state::Set> call_x4_entry_ptr, ret_x4_entry_ptr;
  EntryPtr<state::Set> call_x5_entry_ptr, ret_x5_entry_ptr;

  call_x0_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  call_x1_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  ret_x0_entry_ptr = log.add_ret(call_x0_entry_ptr, state::Set::make_ret(false));
  call_x2_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_x2_entry_ptr = log.add_ret(call_x2_entry_ptr, state::Set::make_ret(false));
  call_x3_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  ret_x3_entry_ptr = log.add_ret(call_x3_entry_ptr, state::Set::make_ret(true));
  call_x4_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_x4_entry_ptr = log.add_ret(call_x4_entry_ptr, state::Set::make_ret(true));
  ret_x1_entry_ptr = log.add_ret(call_x1_entry_ptr, state::Set::make_ret(false));
  call_x5_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_x5_entry_ptr = log.add_ret(call_x5_entry_ptr, state::Set::make_ret(true));

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check());
}

// Let x and y be distinct.
//
// entry id: X0, call: contains(x)
// entry id: X1, call: insert(x)
// entry id: X0, return: ret: 0
// entry id: Y0, call: contains(y) <- not linearizable
// entry id: Y0, return: ret: 1
// entry id: X2, call: contains(x)
// entry id: X2, return: ret: 0
// entry id: X3, call: insert(x)
// entry id: X3, return: ret: 1
// entry id: X4, call: contains(x)
// entry id: X4, return: ret: 1
// entry id: X1, return: ret: 0
// entry id: X5, call: contains(x)
// entry id: X5, return: ret: 1
static void test_014()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  constexpr unsigned not_linearizable_entry_id = 2U;

  Log<state::Set> log{14U};

  EntryPtr<state::Set> call_x0_entry_ptr, ret_x0_entry_ptr;
  EntryPtr<state::Set> call_x1_entry_ptr, ret_x1_entry_ptr;
  EntryPtr<state::Set> call_x2_entry_ptr, ret_x2_entry_ptr;
  EntryPtr<state::Set> call_x3_entry_ptr, ret_x3_entry_ptr;
  EntryPtr<state::Set> call_x4_entry_ptr, ret_x4_entry_ptr;
  EntryPtr<state::Set> call_x5_entry_ptr, ret_x5_entry_ptr;

  EntryPtr<state::Set> call_y0_entry_ptr, ret_y0_entry_ptr;

  call_x0_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  call_x1_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  ret_x0_entry_ptr = log.add_ret(call_x0_entry_ptr, state::Set::make_ret(false));
  call_y0_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  ret_y0_entry_ptr = log.add_ret(call_y0_entry_ptr, state::Set::make_ret(true));
  call_x2_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_x2_entry_ptr = log.add_ret(call_x2_entry_ptr, state::Set::make_ret(false));
  call_x3_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  ret_x3_entry_ptr = log.add_ret(call_x3_entry_ptr, state::Set::make_ret(true));
  call_x4_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_x4_entry_ptr = log.add_ret(call_x4_entry_ptr, state::Set::make_ret(true));
  ret_x1_entry_ptr = log.add_ret(call_x1_entry_ptr, state::Set::make_ret(false));
  call_x5_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_x5_entry_ptr = log.add_ret(call_x5_entry_ptr, state::Set::make_ret(true));

  assert(call_y0_entry_ptr->entry_id() == not_linearizable_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

// Not linearizable:
//
// Let x and y be distinct values.
//
//   contains(x) : false     contains(y) : true
// |---------------------| |--------------------|
//
//                          insert(x) : true
//                    |----------------------------|
static void test_015()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  constexpr unsigned contains_x_entry_id{0U};
  constexpr unsigned insert_x_entry_id{1U};
  constexpr unsigned contains_y_entry_id{2U};

  Log<state::Set> log{6U};

  EntryPtr<state::Set> contains_x_call_entry_ptr, contains_x_ret_entry_ptr;
  EntryPtr<state::Set> insert_x_call_entry_ptr, insert_x_ret_entry_ptr;
  EntryPtr<state::Set> contains_y_call_entry_ptr, contains_y_ret_entry_ptr;

  contains_x_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  insert_x_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  contains_x_ret_entry_ptr = log.add_ret(contains_x_call_entry_ptr, state::Set::make_ret(false));
  contains_y_call_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  contains_y_ret_entry_ptr = log.add_ret(contains_y_call_entry_ptr, state::Set::make_ret(true));
  insert_x_ret_entry_ptr = log.add_ret(insert_x_call_entry_ptr, state::Set::make_ret(true));

  assert(contains_x_call_entry_ptr->entry_id() == contains_x_entry_id);
  assert(contains_x_ret_entry_ptr->entry_id() == contains_x_entry_id);

  assert(insert_x_call_entry_ptr->entry_id() == insert_x_entry_id);
  assert(insert_x_ret_entry_ptr->entry_id() == insert_x_entry_id);

  assert(contains_y_call_entry_ptr->entry_id() == contains_y_entry_id);
  assert(contains_y_ret_entry_ptr->entry_id() == contains_y_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

// Not linearizable:
//
// Let x and y be distinct values.
//
//   contains(x) : false     contains(y) : true     contains(x) : false
// |---------------------| |--------------------| |---------------------|
//
//                             insert(x) : true
//                    |------------------------------|
static void test_016()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  constexpr unsigned not_linearizable_entry_id = 2U;

  Log<state::Set> log{8U};

  EntryPtr<state::Set> call_x0_entry_ptr, ret_x0_entry_ptr;
  EntryPtr<state::Set> call_x1_entry_ptr, ret_x1_entry_ptr;
  EntryPtr<state::Set> call_x2_entry_ptr, ret_x2_entry_ptr;
  EntryPtr<state::Set> call_y0_entry_ptr, ret_y0_entry_ptr;

  call_x0_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  call_x1_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  ret_x0_entry_ptr = log.add_ret(call_x0_entry_ptr, state::Set::make_ret(false));
  call_y0_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  ret_y0_entry_ptr = log.add_ret(call_y0_entry_ptr, state::Set::make_ret(true));
  call_x2_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_x1_entry_ptr = log.add_ret(call_x1_entry_ptr, state::Set::make_ret(true));
  ret_x2_entry_ptr = log.add_ret(call_x2_entry_ptr, state::Set::make_ret(false));

  assert(call_y0_entry_ptr->entry_id() == not_linearizable_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

// Not linearizable:
//
// Let x and y be distinct values.
//
//   contains(x) : false     contains(y) : true     contains(x) : false
// |---------------------| |--------------------| |---------------------|
//
//                                      insert(x) : true
//                    |-----------------------------------------------------|
static void test_017()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  constexpr unsigned not_linearizable_entry_id = 2U;

  Log<state::Set> log{8U};

  EntryPtr<state::Set> call_x0_entry_ptr, ret_x0_entry_ptr;
  EntryPtr<state::Set> call_x1_entry_ptr, ret_x1_entry_ptr;
  EntryPtr<state::Set> call_x2_entry_ptr, ret_x2_entry_ptr;
  EntryPtr<state::Set> call_y0_entry_ptr, ret_y0_entry_ptr;

  call_x0_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  call_x1_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  ret_x0_entry_ptr = log.add_ret(call_x0_entry_ptr, state::Set::make_ret(false));
  call_y0_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  ret_y0_entry_ptr = log.add_ret(call_y0_entry_ptr, state::Set::make_ret(true));
  call_x2_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_x2_entry_ptr = log.add_ret(call_x2_entry_ptr, state::Set::make_ret(false));
  ret_x1_entry_ptr = log.add_ret(call_x1_entry_ptr, state::Set::make_ret(true));

  assert(call_y0_entry_ptr->entry_id() == not_linearizable_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

// Not linearizable:
//
// Let x and y be distinct values.
//
//      contains(y) : true     insert(x) : true
//    |--------------------| |------------------|
//
//                insert(x) : false
// |------------------------------------------------|
static void test_018()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  constexpr unsigned not_linearizable_entry_id = 1U;

  Log<state::Set> log{8U};

  EntryPtr<state::Set> call_x0_entry_ptr, ret_x0_entry_ptr;
  EntryPtr<state::Set> call_x1_entry_ptr, ret_x1_entry_ptr;
  EntryPtr<state::Set> call_y0_entry_ptr, ret_y0_entry_ptr;

  call_x0_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  call_y0_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  ret_y0_entry_ptr = log.add_ret(call_y0_entry_ptr, state::Set::make_ret(true));
  call_x1_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  ret_x1_entry_ptr = log.add_ret(call_x1_entry_ptr, state::Set::make_ret(true));
  ret_x0_entry_ptr = log.add_ret(call_x1_entry_ptr, state::Set::make_ret(false));

  assert(call_y0_entry_ptr->entry_id() == not_linearizable_entry_id);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

// Linearizable:
//
//   insert(x) : insert_ret
// |------------------------|
//
//               contains(x) : contains_ret
//            |-----------------------------|
//
//                 empty() : empty_ret 
//             |------------------------|
static void test_019(bool insert_ret, bool contains_ret, bool empty_ret)
{
  constexpr char x = '\1';

  Log<state::Set> log{8U};

  EntryPtr<state::Set> call_insert_entry_ptr, ret_insert_entry_ptr;
  EntryPtr<state::Set> call_contains_entry_ptr, ret_contains_entry_ptr;
  EntryPtr<state::Set> call_empty_entry_ptr, ret_empty_entry_ptr;

  call_insert_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  call_contains_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  call_empty_entry_ptr = log.add_call(state::Set::make_empty_call());
  ret_insert_entry_ptr = log.add_ret(call_insert_entry_ptr, state::Set::make_ret(insert_ret));
  ret_empty_entry_ptr = log.add_ret(call_empty_entry_ptr, state::Set::make_ret(empty_ret));
  ret_contains_entry_ptr = log.add_ret(call_contains_entry_ptr, state::Set::make_ret(contains_ret));

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == insert_ret);
}

//                                                          insert(x) : insert_ret
//                                                        |------------------------|
//
//   contains(x) :  contains_ret    contains(x) : contains_ret
// |----------------------------| |----------------------------|
//
//                                                     empty() : empty_ret
//                                                   |----------------------|
static void test_020(bool insert_ret, bool contains_ret, bool empty_ret)
{
  constexpr char x = '\1';

  Log<state::Set> log{8U};

  EntryPtr<state::Set> call_contains_0_entry_ptr, ret_contains_0_entry_ptr;
  EntryPtr<state::Set> call_contains_1_entry_ptr, ret_contains_1_entry_ptr;
  EntryPtr<state::Set> call_insert_entry_ptr, ret_insert_entry_ptr;
  EntryPtr<state::Set> call_empty_entry_ptr, ret_empty_entry_ptr;

  call_contains_0_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_contains_0_entry_ptr = log.add_ret(call_contains_0_entry_ptr, state::Set::make_ret(contains_ret));
  call_contains_1_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  call_empty_entry_ptr = log.add_call(state::Set::make_empty_call());
  call_insert_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  ret_contains_1_entry_ptr = log.add_ret(call_contains_1_entry_ptr, state::Set::make_ret(contains_ret));
  ret_empty_entry_ptr = log.add_ret(call_empty_entry_ptr, state::Set::make_ret(empty_ret));
  ret_insert_entry_ptr = log.add_ret(call_insert_entry_ptr, state::Set::make_ret(insert_ret));

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check() == (insert_ret and not contains_ret));
}

// Linearizable:
//
// Let x and y be distinct values.
//
//   contains(x) : false
// |---------------------|
//
//              insert(y) : true
//           |-----------------------------------------------------------|
//
//                            contains(x) : false      empty() : true
//                          |---------------------|  |----------------|
static void test_021()
{
  constexpr char x = '\1';
  constexpr char y = '\2';

  Log<state::Set> log{8U};

  EntryPtr<state::Set> call_contains_0_entry_ptr, ret_contains_0_entry_ptr;
  EntryPtr<state::Set> call_contains_1_entry_ptr, ret_contains_1_entry_ptr;
  EntryPtr<state::Set> call_insert_entry_ptr, ret_insert_entry_ptr;
  EntryPtr<state::Set> call_empty_entry_ptr, ret_empty_entry_ptr;

  call_contains_0_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  call_insert_entry_ptr = log.add_call(state::Set::make_insert_call(y));
  ret_contains_0_entry_ptr = log.add_ret(call_contains_0_entry_ptr, state::Set::make_ret(false));
  call_contains_1_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  ret_contains_1_entry_ptr = log.add_ret(call_contains_1_entry_ptr, state::Set::make_ret(false));
  call_empty_entry_ptr = log.add_call(state::Set::make_empty_call());
  ret_empty_entry_ptr = log.add_ret(call_empty_entry_ptr, state::Set::make_ret(true));
  ret_insert_entry_ptr = log.add_ret(call_insert_entry_ptr, state::Set::make_ret(1));

  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check());
}

// Linearizable:
//
//        push(x) : true
// |------------------------|
//
//        push(y) : true
//   |--------------------|
//
//      pop() : (true, x)
//    |------------------|
static void test_stack_history_000()
{
  constexpr char x = '\1';
  constexpr char y = '\2';
  constexpr std::size_t N = 5;

  Log<state::Stack<N>> log{6U};
  EntryPtr<state::Stack<N>> try_push_x_call_entry_ptr, try_push_x_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_push_y_call_entry_ptr, try_push_y_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_pop_x_call_entry_ptr, try_pop_x_ret_entry_ptr;

  try_push_x_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(x));
  try_push_y_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(y));
  try_pop_x_call_entry_ptr = log.add_call(state::Stack<N>::make_try_pop_call());
  try_push_x_ret_entry_ptr = log.add_ret(try_push_x_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));
  try_push_y_ret_entry_ptr = log.add_ret(try_push_y_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));
  try_pop_x_ret_entry_ptr = log.add_ret(try_pop_x_call_entry_ptr, state::Stack<N>::make_try_pop_ret(true, x));

  assert(try_push_x_call_entry_ptr->is_partitionable());
  assert(try_push_y_call_entry_ptr->is_partitionable());
  assert(try_pop_x_call_entry_ptr->is_partitionable());

  assert(try_push_x_ret_entry_ptr->is_partitionable());
  assert(try_push_y_ret_entry_ptr->is_partitionable());
  assert(try_pop_x_ret_entry_ptr->is_partitionable());

  LinearizabilityTester<state::Stack<N>> t{log.info()};
  assert(t.check());
}

// push(x):true; push(y):true; pop():x
static void test_stack_history_001()
{
  constexpr char x = '\1';
  constexpr char y = '\2';
  constexpr std::size_t N = 5;

  Log<state::Stack<N>> log{6U};
  EntryPtr<state::Stack<N>> try_push_x_call_entry_ptr, try_push_x_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_push_y_call_entry_ptr, try_push_y_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_pop_x_call_entry_ptr, try_pop_x_ret_entry_ptr;

  try_push_x_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(x));
  try_push_x_ret_entry_ptr = log.add_ret(try_push_x_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));
  try_push_y_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(y));
  try_push_y_ret_entry_ptr = log.add_ret(try_push_y_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));
  try_pop_x_call_entry_ptr = log.add_call(state::Stack<N>::make_try_pop_call());
  try_pop_x_ret_entry_ptr = log.add_ret(try_pop_x_call_entry_ptr, state::Stack<N>::make_try_pop_ret(true, x));

  assert(try_push_x_call_entry_ptr->is_partitionable());
  assert(try_push_y_call_entry_ptr->is_partitionable());
  assert(try_pop_x_call_entry_ptr->is_partitionable());

  assert(try_push_x_ret_entry_ptr->is_partitionable());
  assert(try_push_y_ret_entry_ptr->is_partitionable());
  assert(try_pop_x_ret_entry_ptr->is_partitionable());

  LinearizabilityTester<state::Stack<N>> t{log.info()};
  assert(not t.check());
}

// entry id: 0, thread id: 0x2, call: try_push(x)
// entry id: 0, thread id: 0x2, return: ret: 1
// entry id: 1, thread id: 0x3, call: try_push(y)
// entry id: 2, thread id: 0x4, call: try_pop()
// entry id: 2, thread id: 0x4, return: ret: [ok: 1, value: x]
// entry id: 1, thread id: 0x3, return: ret: 1
static void test_stack_history_002()
{
  constexpr char x = '\1';
  constexpr char y = '\2';
  constexpr std::size_t N = 5;

  Log<state::Stack<N>> log{8U};
  EntryPtr<state::Stack<N>> try_push_x_call_entry_ptr, try_push_x_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_push_y_call_entry_ptr, try_push_y_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_pop_x_call_entry_ptr, try_pop_x_ret_entry_ptr;

  try_push_x_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(x));
  try_push_x_ret_entry_ptr = log.add_ret(try_push_x_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));
  try_push_y_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(y));
  try_pop_x_call_entry_ptr = log.add_call(state::Stack<N>::make_try_pop_call());
  try_pop_x_ret_entry_ptr = log.add_ret(try_pop_x_call_entry_ptr, state::Stack<N>::make_try_pop_ret(true, x));
  try_push_y_ret_entry_ptr = log.add_ret(try_push_y_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));

  assert(try_push_x_call_entry_ptr->is_partitionable());
  assert(try_push_y_call_entry_ptr->is_partitionable());
  assert(try_pop_x_call_entry_ptr->is_partitionable());

  assert(try_push_x_ret_entry_ptr->is_partitionable());
  assert(try_push_y_ret_entry_ptr->is_partitionable());
  assert(try_pop_x_ret_entry_ptr->is_partitionable());

  assert(try_push_x_call_entry_ptr->op().partition() == x);
  assert(try_push_y_call_entry_ptr->op().partition() == y);
  assert(try_pop_x_call_entry_ptr->op().partition() == x);

  assert(try_push_x_ret_entry_ptr->op().partition() == x);
  assert(try_push_y_ret_entry_ptr->op().partition() == y);
  assert(try_pop_x_ret_entry_ptr->op().partition() == x);

  LinearizabilityTester<state::Stack<N>> t{log.info()};
  assert(t.check());
}

// Linearizable:
//
//   push(x) : true       pop() : (true, y)
// |----------------|   |------------------|
//
//     push(y) : true                           push(z) : true
//   |----------------|                |---------------------------------|
//
//                                                  pop() : (true, x)     pop() : (true, z)
//                                               |-------------------| |-------------------|
static void test_stack_history_003()
{
  constexpr char x = '\1';
  constexpr char y = '\2';
  constexpr char z = '\3';
  constexpr std::size_t N = 5;

  Log<state::Stack<N>> log{12U};
  EntryPtr<state::Stack<N>> try_push_x_call_entry_ptr, try_push_x_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_push_y_call_entry_ptr, try_push_y_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_push_z_call_entry_ptr, try_push_z_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_pop_x_call_entry_ptr, try_pop_x_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_pop_y_call_entry_ptr, try_pop_y_ret_entry_ptr;
  EntryPtr<state::Stack<N>> try_pop_z_call_entry_ptr, try_pop_z_ret_entry_ptr;

  try_push_x_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(x));
  try_push_y_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(y));
  try_push_x_ret_entry_ptr = log.add_ret(try_push_x_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));
  try_push_y_ret_entry_ptr = log.add_ret(try_push_y_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));
  try_pop_y_call_entry_ptr = log.add_call(state::Stack<N>::make_try_pop_call());
  try_push_z_call_entry_ptr = log.add_call(state::Stack<N>::make_try_push_call(z));
  try_pop_y_ret_entry_ptr = log.add_ret(try_pop_y_call_entry_ptr, state::Stack<N>::make_try_pop_ret(true, y));
  try_pop_x_call_entry_ptr = log.add_call(state::Stack<N>::make_try_pop_call());
  try_pop_x_ret_entry_ptr = log.add_ret(try_pop_x_call_entry_ptr, state::Stack<N>::make_try_pop_ret(true, x));
  try_pop_z_call_entry_ptr = log.add_call(state::Stack<N>::make_try_pop_call());
  try_push_z_ret_entry_ptr = log.add_ret(try_push_z_call_entry_ptr, state::Stack<N>::make_try_push_ret(true));
  try_pop_z_ret_entry_ptr = log.add_ret(try_pop_z_call_entry_ptr, state::Stack<N>::make_try_pop_ret(true, z));

  LinearizabilityTester<state::Stack<N>> t{log.info()};
  assert(t.check());
}


// Let x = '\0' and y = '\1'.
//
//   erase(x) : false     insert(y) : true
// |------------------| |------------------|
//
//                                               contains(x) : true
//                                 |------------------------------------------------|
//
//                                      contains(y) : false     insert(x) : true
//                                    |---------------------| |------------------|
static void test_slice_000()
{
  constexpr char x = '\0';
  constexpr char y = '\1';

  Log<state::Set> log{10U};

  EntryPtr<state::Set> erase_x_call_entry_ptr, erase_x_ret_entry_ptr;
  EntryPtr<state::Set> insert_x_call_entry_ptr, insert_x_ret_entry_ptr;
  EntryPtr<state::Set> contains_x_call_entry_ptr, contains_x_ret_entry_ptr;
  EntryPtr<state::Set> insert_y_call_entry_ptr, insert_y_ret_entry_ptr;
  EntryPtr<state::Set> contains_y_call_entry_ptr, contains_y_ret_entry_ptr;

  erase_x_call_entry_ptr = log.add_call(state::Set::make_erase_call(x));
  erase_x_ret_entry_ptr = log.add_ret(erase_x_call_entry_ptr, state::Set::make_ret(false));
  insert_y_call_entry_ptr = log.add_call(state::Set::make_insert_call(y));
  contains_x_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_y_call_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  insert_y_ret_entry_ptr = log.add_ret(insert_y_call_entry_ptr, state::Set::make_ret(true));
  contains_y_ret_entry_ptr = log.add_ret(contains_y_call_entry_ptr, state::Set::make_ret(false));
  insert_x_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));
  insert_x_ret_entry_ptr = log.add_ret(insert_x_call_entry_ptr, state::Set::make_ret(true));
  contains_x_ret_entry_ptr = log.add_ret(contains_x_call_entry_ptr, state::Set::make_ret(true));

  Slicer<state::Set> slicer{log.info(), 2U};

  assert(slicer.sublog_info(x).log_head_ptr() == erase_x_call_entry_ptr);
  assert(slicer.sublog_info(y).log_head_ptr() == insert_y_call_entry_ptr);

  assert(slicer.sublog_info(x).number_of_entries() == 6U);
  assert(slicer.sublog_info(y).number_of_entries() == 4U);

  LinearizabilityTester<state::Set> tester_0{slicer.sublog_info(x)};
  assert(tester_0.check());

  LinearizabilityTester<state::Set> tester_1{slicer.sublog_info(y)};
  assert(tester_1.check());
}

// Let x = '\0' and y = '\1'.
//
//   contains(x) : false 
// |---------------------|
//
//      contains(y) : false
//    |---------------------|
//
//          insert(x) : false
//        |---------------------|
static void test_slice_001()
{
  constexpr char x = '\0';
  constexpr char y = '\1';

  Log<state::Set> log{6U};
  EntryPtr<state::Set> contains_x_call_entry_ptr, contains_x_ret_entry_ptr;
  EntryPtr<state::Set> contains_y_call_entry_ptr, contains_y_ret_entry_ptr;
  EntryPtr<state::Set> insert_x_call_entry_ptr, insert_x_ret_entry_ptr;

  contains_x_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_y_call_entry_ptr = log.add_call(state::Set::make_contains_call(y));
  insert_x_call_entry_ptr = log.add_call(state::Set::make_insert_call(x));

  contains_x_ret_entry_ptr = log.add_ret(contains_x_call_entry_ptr, state::Set::make_ret(false));
  contains_y_ret_entry_ptr = log.add_ret(contains_y_call_entry_ptr, state::Set::make_ret(false));
  insert_x_ret_entry_ptr = log.add_ret(insert_x_call_entry_ptr, state::Set::make_ret(false));

  Slicer<state::Set> slicer{log.info(), 2U};

  assert(slicer.sublog_info(x).log_head_ptr() == contains_x_call_entry_ptr);
  assert(slicer.sublog_info(y).log_head_ptr() == contains_y_call_entry_ptr);

  assert(slicer.sublog_info(x).number_of_entries() == 4U);
  assert(slicer.sublog_info(y).number_of_entries() == 2U);

  LinearizabilityTester<state::Set> tester_0{slicer.sublog_info(x)};
  assert(not tester_0.check());

  LinearizabilityTester<state::Set> tester_1{slicer.sublog_info(y)};
  assert(tester_1.check());
}

#ifdef _LT_DEBUG_

#ifdef __clang__
#define INIT_THREAD_ID "0x0"
#else
#define INIT_THREAD_ID "thread::id of a non-executing thread"
#endif

static void debug()
{
  constexpr char x = '\1';

  Log<state::Set> log{2U};

  EntryPtr<state::Set> contains_call_entry_ptr, contains_ret_entry_ptr;
  contains_call_entry_ptr = log.add_call(state::Set::make_contains_call(x));
  contains_ret_entry_ptr = log.add_ret(contains_call_entry_ptr, state::Set::make_ret(true));

  LinearizabilityTester<state::Set> t{log.info()};
  Result<state::Set> result;

  t.check(result);
  assert(not result.is_linearizable());

  std::stringstream os;
  result.debug(os);

  assert(os.str() == "Linearizable: No\n"
    "entry id: 0, thread id: " INIT_THREAD_ID ", call: contains(1)\n"
    "^ previous entries cannot be linearized\n"
    "entry id: 0, thread id: " INIT_THREAD_ID ", return: ret: 1\n"
    "^ previous entries cannot be linearized\n");
}
#endif

static void concurrent_log()
{
  constexpr unsigned number_of_partitions = 1U;

  constexpr char x = '\0';

  ConcurrentLog<state::Set> log{6U};

  EntryPtr<state::Set> contains_x_call_entry_ptr, contains_x_ret_entry_ptr;
  EntryPtr<state::Set> insert_x_call_entry_ptr, insert_x_ret_entry_ptr;

  contains_x_call_entry_ptr = log.push_back(state::Set::make_contains_call(x));
  insert_x_call_entry_ptr = log.push_back(state::Set::make_insert_call(x));
  contains_x_ret_entry_ptr = log.push_back(contains_x_call_entry_ptr, state::Set::make_ret(false));
  insert_x_ret_entry_ptr = log.push_back(insert_x_call_entry_ptr, state::Set::make_ret(false));

  EntryPtr<state::Set> entry_ptr, log_head_ptr{log.log_head_ptr()};

  assert(log_head_ptr == contains_x_call_entry_ptr);
  assert(log_head_ptr->prev == nullptr);
  assert(log_head_ptr->next == insert_x_call_entry_ptr);
  assert(log_head_ptr->match() == contains_x_ret_entry_ptr);

  entry_ptr = log_head_ptr->next;
  assert(entry_ptr == insert_x_call_entry_ptr);
  assert(entry_ptr->prev == contains_x_call_entry_ptr);
  assert(entry_ptr->next == contains_x_ret_entry_ptr);
  assert(entry_ptr->match() == insert_x_ret_entry_ptr);

  entry_ptr = entry_ptr->next;
  assert(entry_ptr == contains_x_ret_entry_ptr);
  assert(entry_ptr->prev == insert_x_call_entry_ptr);
  assert(entry_ptr->next == insert_x_ret_entry_ptr);
  assert(entry_ptr->match() == contains_x_call_entry_ptr);

  entry_ptr = entry_ptr->next;
  assert(entry_ptr == insert_x_ret_entry_ptr);
  assert(entry_ptr->prev == contains_x_ret_entry_ptr);
  assert(entry_ptr->next == nullptr);
  assert(entry_ptr->match() == insert_x_call_entry_ptr);

  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check());
}

struct WorkerConfiguration
{
  const char max_value;
  const unsigned number_of_ops;
};

static void returns_always_false_worker(
  const WorkerConfiguration& worker_configuration,
  ConcurrentLog<state::Set>& concurrent_log)
{
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<> value_dist('\0', worker_configuration.max_value);
  std::uniform_int_distribution<> percentage_dist(0, 100);

  // each operation returns false
  constexpr bool ret = false;

  char value;
  EntryPtr<state::Set> call_entry_ptr;
  for (unsigned number_of_ops{0U};
       number_of_ops < worker_configuration.number_of_ops;
       ++number_of_ops)
  {
    value = value_dist(rd);
    if (percentage_dist(rd) < 30)
    {
      call_entry_ptr = concurrent_log.push_back(state::Set::make_insert_call(value));
      concurrent_log.push_back(call_entry_ptr, state::Set::make_ret(ret));
    }
    else if (percentage_dist(rd) < 50)
    {
      call_entry_ptr = concurrent_log.push_back(state::Set::make_erase_call(value));
      concurrent_log.push_back(call_entry_ptr, state::Set::make_ret(ret));
    }
    else
    {
      call_entry_ptr = concurrent_log.push_back(state::Set::make_contains_call(value));
      concurrent_log.push_back(call_entry_ptr, state::Set::make_ret(ret));
    }
  }
}

template<class F, class ...Args>
void start_threads(unsigned number_of_threads, F&& f, Args&&... args)
{
  std::vector<Thread> threads(number_of_threads);

  for (Thread& thread : threads)
    thread = Thread(std::forward<F>(f), std::forward<Args>(args)...);

  for (Thread& thread : threads)
    thread.join();
}

/// The first "insert" operation should be always marked as non-linearizable.
static void fuzzy_functional_test()
{
  constexpr unsigned number_of_threads = 4U;
  constexpr WorkerConfiguration worker_configuration = {'\7', 12U};
  constexpr unsigned log_size = number_of_threads * worker_configuration.number_of_ops;

  ConcurrentLog<state::Set> concurrent_log{2U * log_size};

  // create history
  start_threads(number_of_threads, returns_always_false_worker,
    std::cref(worker_configuration), std::ref(concurrent_log));

  LinearizabilityTester<state::Set> tester{concurrent_log.info()};

  assert(not tester.check());
}

template<class S>
std::string mem_usage(const Result<S>& result)
{
#ifdef _LT_MEM_USAGE_
  static std::string s_vm = "[Virtual memory: ";
  static std::string s_rss = " MiB; Resident set size: ";
  static std::string s_end = " MiB]";

  std::stringstream buff;
  buff << s_vm << result.virtual_memory_usage()
       << s_rss << result.resident_set_size() << s_end;

  return buff.str();
#else
  static std::string s_empty = "";
  return s_empty;
#endif
}

#ifdef _ENABLE_EMBB_
template<std::size_t N>
static void embb_worker(
  const WorkerConfiguration& worker_configuration,
  ConcurrentLog<state::Stack<N>>& concurrent_log,
  embb::containers::LockFreeStack<char>& concurrent_stack)
{
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<> value_dist('\0', worker_configuration.max_value);
  std::uniform_int_distribution<> percentage_dist(0, 100);

  // each operation returns false
  bool ret;

  char value;
  unsigned percentage;
  EntryPtr<state::Stack<N>> call_entry_ptr;
  for (unsigned number_of_ops{0U};
       number_of_ops < worker_configuration.number_of_ops;
       ++number_of_ops)
  {
    value = value_dist(rd);
    percentage = percentage_dist(rd);
    if (percentage < 30)
    {
      call_entry_ptr = concurrent_log.push_back(state::Stack<N>::make_try_push_call(value));
      ret = concurrent_stack.TryPush(value);
      concurrent_log.push_back(call_entry_ptr, state::Stack<N>::make_try_push_ret(ret));
    }
    else
    {
      call_entry_ptr = concurrent_log.push_back(state::Stack<N>::make_try_pop_call());
      ret = concurrent_stack.TryPop(value);
      concurrent_log.push_back(call_entry_ptr, state::Stack<N>::make_try_pop_ret(ret, value));
    }
  }
}

static void embb_experiment(bool is_linearizable)
{
  constexpr std::chrono::hours max_duration{1};
  constexpr std::size_t N = 3000000U;
  constexpr unsigned number_of_threads = 4U;
  constexpr WorkerConfiguration worker_configuration = {'\27', 70000U};
  constexpr unsigned log_size = number_of_threads * worker_configuration.number_of_ops;

  std::cout << "embb_experiment : " << (is_linearizable ? "" : "not ") << "linearizable" << std::endl;

  Result<state::Stack<N>> result;
  ConcurrentLog<state::Stack<N>> concurrent_log{2U * log_size};
  embb::containers::LockFreeStack<char> concurrent_stack(N);

  if (not is_linearizable)
  {
    bool ok = concurrent_stack.TryPush(5);
    assert(ok);
  }

  // create history
  start_threads(number_of_threads, embb_worker<N>, std::cref(worker_configuration),
    std::ref(concurrent_log), std::ref(concurrent_stack));

  const LogInfo<state::Stack<N>> log_info{concurrent_log.info()};
  // std::cout << log_info << std::endl;

  auto start = std::chrono::system_clock::now();
  auto end = std::chrono::system_clock::now();
  std::chrono::seconds seconds;

  start = std::chrono::system_clock::now();
  {
    Log<state::Stack<N>> log_copy{log_info};
    LinearizabilityTester<state::Stack<N>, true> tester{log_copy.info(), max_duration};
    tester.check(result);
    assert(result.is_timeout() or result.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, enabled state cache (LRU=on), O(1) hash: " << seconds.count() << " s " << mem_usage(result) << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Stack<N>> log_copy{log_info};
    LinearizabilityTester<state::Stack<N>, false> tester{log_copy.info(), max_duration};
    tester.check(result);
    assert(result.is_timeout() or result.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, enabled state cache (LRU=off), O(1) hash: " << seconds.count() << " s " << mem_usage(result) << std::endl;
}
#endif

#ifdef _ENABLE_TBB_
// Calls only contains() and insert() on set ADT
static void tbb_comprehensive_worker(
  const WorkerConfiguration& worker_configuration,
  ConcurrentLog<state::Set>& concurrent_log,
  tbb::concurrent_unordered_set<char>& concurrent_set)
{
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<> value_dist('\0', worker_configuration.max_value);
  std::uniform_int_distribution<> percentage_dist(0, 100);

  // each operation returns false
  bool ret;

  char value;
  EntryPtr<state::Set> call_entry_ptr;
  for (unsigned number_of_ops{0U};
       number_of_ops < worker_configuration.number_of_ops;
       ++number_of_ops)
  {
    value = value_dist(rd);
    if (percentage_dist(rd) < 30)
    {
      call_entry_ptr = concurrent_log.push_back(state::Set::make_insert_call(value));
      ret = std::get<1>(concurrent_set.insert(value));
      concurrent_log.push_back(call_entry_ptr, state::Set::make_ret(ret));
    }
    else
    {
      call_entry_ptr = concurrent_log.push_back(state::Set::make_contains_call(value));
      ret = concurrent_set.find(value) != concurrent_set.end();
      concurrent_log.push_back(call_entry_ptr, state::Set::make_ret(ret));
    }
  }
}

// Calls empty(), contains() and insert() on set ADT
static void tbb_worker(
  const WorkerConfiguration& worker_configuration,
  ConcurrentLog<state::Set>& concurrent_log,
  tbb::concurrent_unordered_set<char>& concurrent_set)
{
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<> value_dist('\0', worker_configuration.max_value);
  std::uniform_int_distribution<> percentage_dist(0, 100);

  // each operation returns false
  bool ret;

  char value;
  unsigned percentage;
  EntryPtr<state::Set> call_entry_ptr;
  for (unsigned number_of_ops{0U};
       number_of_ops < worker_configuration.number_of_ops;
       ++number_of_ops)
  {
    value = value_dist(rd);
    percentage = percentage_dist(rd);
    if (percentage < 30)
    {
      call_entry_ptr = concurrent_log.push_back(state::Set::make_insert_call(value));
      ret = std::get<1>(concurrent_set.insert(value));
      concurrent_log.push_back(call_entry_ptr, state::Set::make_ret(ret));
    }
    else if (percentage < 50)
    {
      call_entry_ptr = concurrent_log.push_back(state::Set::make_empty_call());
      ret = concurrent_set.empty();
      concurrent_log.push_back(call_entry_ptr, state::Set::make_ret(ret));
    }
    else
    {
      call_entry_ptr = concurrent_log.push_back(state::Set::make_contains_call(value));
      ret = concurrent_set.find(value) != concurrent_set.end();
      concurrent_log.push_back(call_entry_ptr, state::Set::make_ret(ret));
    }
  }
}

static void tbb_functional_test(bool is_linearizable)
{
  constexpr unsigned number_of_threads = 4U;
  constexpr WorkerConfiguration worker_configuration = {'\27', 1000U};
  constexpr unsigned log_size = number_of_threads * worker_configuration.number_of_ops;

  Result<state::Set> result;
  ConcurrentLog<state::Set> concurrent_log{2U * log_size};
  tbb::concurrent_unordered_set<char> concurrent_set;

  if (not is_linearizable)
  {
    auto pair = concurrent_set.insert(5);
    assert(pair.second);
  }

  // create history
  start_threads(number_of_threads, tbb_worker, std::cref(worker_configuration),
    std::ref(concurrent_log), std::ref(concurrent_set));

  LinearizabilityTester<state::Set> tester{concurrent_log.info()};
  tester.check(result);
  assert(result.is_timeout() or result.is_linearizable() == is_linearizable);
}

static void tbb_experiment(bool is_linearizable)
{
  constexpr std::chrono::hours max_duration{1};
  constexpr unsigned number_of_threads = 4U;
  constexpr WorkerConfiguration worker_configuration = {'\27', 70000U};
  constexpr unsigned log_size = number_of_threads * worker_configuration.number_of_ops;

  std::cout << "tbb_experiment : " << (is_linearizable ? "" : "not ") << "linearizable" << std::endl;

  ConcurrentLog<state::Set> concurrent_log{2U * log_size};
  tbb::concurrent_unordered_set<char> concurrent_set;

  if (not is_linearizable)
  {
    auto pair = concurrent_set.insert(5);
    assert(pair.second);
  }

  // create history
  start_threads(number_of_threads, tbb_worker, std::cref(worker_configuration),
    std::ref(concurrent_log), std::ref(concurrent_set));

  Result<state::Set> result;
  const LogInfo<state::Set> log_info{concurrent_log.info()};
  // std::cout << log_info << std::endl;

  auto start = std::chrono::system_clock::now();
  auto end = std::chrono::system_clock::now();
  std::chrono::seconds seconds;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, true> tester{log_copy.info(), max_duration};
    tester.check(result);
    assert(result.is_timeout() or result.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, enabled state cache (LRU=on), O(1) hash: " << seconds.count() << " s " << mem_usage(result) << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, false> tester{log_copy.info(), max_duration};
    tester.check(result);
    assert(result.is_timeout() or result.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, enabled state cache (LRU=off), O(1) hash: " << seconds.count() << " s " << mem_usage(result) << std::endl;
}

/// Run as many different kinds of linearizability testers as possible
static void tbb_comprehensive_experiment(bool is_linearizable)
{
  constexpr std::chrono::hours max_duration{1};
  constexpr unsigned number_of_threads = 4U;
  constexpr WorkerConfiguration worker_configuration = {'\27', 70000U};
  constexpr unsigned log_size = number_of_threads * worker_configuration.number_of_ops;

  std::cout << "tbb_comprehensive_experiment : " << (is_linearizable ? "" : "not ") << "linearizable" << std::endl;

  Result<state::Set> result;
  ConcurrentLog<state::Set> concurrent_log{2U * log_size};
  tbb::concurrent_unordered_set<char> concurrent_set;

  if (not is_linearizable)
  {
    auto pair = concurrent_set.insert(5);
    assert(pair.second);
  }

  // create history
  start_threads(number_of_threads, tbb_comprehensive_worker, std::cref(worker_configuration),
    std::ref(concurrent_log), std::ref(concurrent_set));

  const LogInfo<state::Set> log_info{concurrent_log.info()};
  // std::cout << log_info << std::endl;

  auto start = std::chrono::system_clock::now();
  auto end = std::chrono::system_clock::now();
  std::chrono::seconds seconds;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, true> tester{log_copy.info(), max_duration};
    tester.check(result);
    assert(result.is_timeout() or result.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, enabled state cache (LRU=on), O(1) hash: " << seconds.count() << " s " << mem_usage(result) << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, false> tester{log_copy.info(), max_duration};
    tester.check(result);
    assert(result.is_timeout() or result.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, enabled state cache (LRU=off), O(1) hash: " << seconds.count() << " s " << mem_usage(result) << std::endl;

  const unsigned number_of_partitions{worker_configuration.max_value + 1U};

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    Slicer<state::Set> slicer{log_copy.info(), number_of_partitions};
    bool r{true};
    for (unsigned partition = 0; partition < slicer.number_of_partitions; ++partition)
    {
      LinearizabilityTester<state::Set> tester{slicer.sublog_info(partition), max_duration};
      if (not tester.check())
      {
        r = false;
        break;
      }
    }
    assert(r == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Compositional: " << seconds.count() << " s " << mem_usage(result) << std::endl;
}
#endif

static void test_parse_jepsen_etcd()
{
  static constexpr char s_snippet[] = ""
    "INFO  jepsen.util - 3	:invoke	:read	nil\n"
    "INFO  jepsen.util - 2	:invoke	:write	4\n"
    "INFO  jepsen.util - 3	:ok	:read	nil\n"
    "INFO  jepsen.util - 2	:ok	:write	4\n"
    "INFO  jepsen.util - 3	:invoke	:write	3\n"
    "INFO  jepsen.util - 0	:invoke	:read	nil\n"
    "INFO  jepsen.util - 0	:ok	:read	3\n"
    "INFO  jepsen.util - 3	:ok	:write	3\n"
    "INFO  jepsen.util - 2	:invoke	:cas	[3 0]\n"
    "INFO  jepsen.util - 2	:ok	:cas	[3 0]\n"
    "INFO  jepsen.util - 1	:invoke	:cas	[0 3]\n"
    "INFO  jepsen.util - 1	:fail	:cas	[0 3]\n"
    "INFO  jepsen.util - :nemesis	:info	:start	nil\n"
    "INFO  jepsen.util - 4	:invoke	:write	2\n"
    "INFO  jepsen.util - 4	:ok	:write	2\n"
    "INFO  jepsen.util - :nemesis	:info	:start	\"Cut off {:n1 #{:n2 :n5}, :n4 #{:n2 :n5}, :n3 #{:n2 :n5}, :n5 #{:n3 :n4 :n1}, :n2 #{:n3 :n4 :n1}}\"\n"
    "INFO  jepsen.util - 4	:invoke	:write	1\n"
    "INFO  jepsen.util - 1	:invoke	:cas	[2 1]\n"
    "INFO  jepsen.util - 4	:info	:write	:timed-out\n"
    "INFO  jepsen.util - 1	:info	:cas	:timed-out\n"
    "INFO  jepsen.util - :nemesis	:info	:stop	nil\n"
    "INFO  jepsen.util - :nemesis	:info	:stop	\"fully connected\"\n"
    "INFO  jepsen.util - 0	:invoke	:read	nil\n"
    "INFO  jepsen.util - 0	:ok	:read	3\n";

  std::stringstream istream, ostream;
  JepsenEtcdParser jepsen_etcd_parser;
  istream << s_snippet;
  jepsen_etcd_parser.parse(istream);

  ostream << jepsen_etcd_parser.log.info();

  // for now, we ignore thread ids because they are not
  // essential for the linearizability algorithm
  assert(ostream.str() == "log info, number of entries: 20\n"
    "entry id: 0, thread id: 0x0, call: read()\n"
    "entry id: 1, thread id: 0x0, call: write(4)\n"
    "entry id: 0, thread id: 0x0, return: read() : -1\n"
    "entry id: 1, thread id: 0x0, return: write() : succeeded\n"
    "entry id: 2, thread id: 0x0, call: write(3)\n"
    "entry id: 3, thread id: 0x0, call: read()\n"
    "entry id: 3, thread id: 0x0, return: read() : 3\n"
    "entry id: 2, thread id: 0x0, return: write() : succeeded\n"
    "entry id: 4, thread id: 0x0, call: cas(3, 0)\n"
    "entry id: 4, thread id: 0x0, return: cas() : succeeded\n"
    "entry id: 5, thread id: 0x0, call: cas(0, 3)\n"
    "entry id: 5, thread id: 0x0, return: cas() : failed\n"
    "entry id: 6, thread id: 0x0, call: write(2)\n"
    "entry id: 6, thread id: 0x0, return: write() : succeeded\n"
    "entry id: 7, thread id: 0x0, call: write(1)\n"
    "entry id: 8, thread id: 0x0, call: cas(2, 1)\n"
    "entry id: 9, thread id: 0x0, call: read()\n"
    "entry id: 9, thread id: 0x0, return: read() : 3\n"
    "entry id: 7, thread id: 0x0, return: write() : pending\n"
    "entry id: 8, thread id: 0x0, return: cas() : pending\n");

  LinearizabilityTester<state::Atomic> t{jepsen_etcd_parser.log.info()};

  // failed CAS cannot be linearized
  assert(not t.check());
}

// Cache eviction in the linearizability tester must be disabled for
// this test to complete within a reasonable amount of time.
static void test_jepsen_etcd()
{
  static constexpr char s_etcd_prefix[] = "jepsen/etcd_";
  static constexpr char s_etcd_postfix[] = ".log";

  unsigned i{0};
  std::string zeros, filename;
  Result<state::Atomic> result;

  bool expected[] = { false, // 000
                      false, // 001
                      true,  // 002
                      false, // 003
                      false, // 004
                      true,  // 005
                      false, // 006
                      true,  // 007
                      false, // 008
                      false, // 009
                      false, // 010
                      false, // 011
                      false, // 012
                      false, // 013
                      false, // 014
                      false, // 015
                      false, // 016
                      false, // 017
                      true,  // 018
                      false, // 019
                      false, // 020
                      false, // 021
                      false, // 022
                      false, // 023
                      false, // 024
                      true,  // 025
                      false, // 026
                      false, // 027
                      false, // 028
                      false, // 029
                      false, // 030
                      true,  // 031
                      false, // 032
                      false, // 033
                      false, // 034
                      false, // 035
                      false, // 036
                      false, // 037
                      true,  // 038
                      false, // 039
                      false, // 040
                      false, // 041
                      false, // 042
                      false, // 043
                      false, // 044
                      true,  // 045
                      false, // 046
                      false, // 047
                      true,  // 048
                      true,  // 049
                      false, // 050
                      true,  // 051
                      false, // 052
                      true,  // 053
                      false, // 054
                      false, // 055
                      true,  // 056
                      false, // 057
                      false, // 058
                      false, // 059
                      false, // 060
                      false, // 061
                      false, // 062
                      false, // 063
                      false, // 064
                      false, // 065
                      false, // 066
                      true,  // 067
                      false, // 068
                      false, // 069
                      false, // 070
                      false, // 071
                      false, // 072
                      false, // 073
                      false, // 074
                      true,  // 075
                      true,  // 076
                      false, // 077
                      false, // 078
                      false, // 079
                      true,  // 080
                      false, // 081
                      false, // 082
                      false, // 083
                      false, // 084
                      false, // 085
                      false, // 086
                      true,  // 087
                      false, // 088
                      false, // 089
                      false, // 090
                      false, // 091
                      true,  // 092
                      false, // 093
                      false, // 094
                      false, // 095
                      false, // 096
                      false, // 097
                      true,  // 098
                      false, // 099
                    };

  for (bool expect : expected)
  {

    // etcd cluster failed to start up in benchmark 95
    if (i == 95)
    {
      ++i;
      continue;
    }

    zeros = "";
    if (i < 10U)
      zeros = std::string(2, '0');
    else if (i < 100U)
      zeros = std::string(1, '0');

    std::ifstream file;
    filename = s_etcd_prefix + zeros + std::to_string(i) + s_etcd_postfix;
    file.open(filename);
    assert(file.is_open());

    std::cout << filename << std::endl;
    JepsenEtcdParser jepsen_etcd_parser;
    jepsen_etcd_parser.parse(file);

    LinearizabilityTester<state::Atomic> t{jepsen_etcd_parser.log.info()};
    t.check(result);
    assert(result.is_linearizable() == expect);

    ++i;
  }
}

int main()
{
  test_lru_cache();
  test_atomic_op();
  test_stack();
  test_state_set();
  test_bitset();
  test_state_set_op();
  test_state_stack();
  test_state_stack_op();

  test_linearizability_empty_log();
  test_raw_single_contains_is_linearizable();
  test_raw_single_contains_is_not_linearizable();
  test_log_copy();
  test_single_contains(true);
  test_single_contains(false);

  // Consider a sequential insert(x) and contains(x) operation
  // and their return values on an initially empty set:

  for (bool a : {true, false})
    for (bool b : {true, false})
    {
      test_000(a, b);
      test_001(a, b);
      test_002(a, b);
      test_003(a, b);
      test_004(a, b);
      test_005(a, b);
      test_006(a, b);
      test_007(a, b);
      test_008(a, b);
    }

  // semantically deeper tests

  test_009();
  test_010();
  test_011();
  test_012();
  test_013();
  test_014();
  test_015();
  test_016();
  test_017();
  test_018();

  for (bool a : {true, false})
    for (bool b : {true, false})
      for (bool c : {true, false})
      {
        test_019(a, b, c);
        test_020(a, b, c);
      }

  test_021();

  test_stack_history_000();
  test_stack_history_001();
  test_stack_history_002();
  test_stack_history_003();

  test_slice_000();
  test_slice_001();

#ifdef _LT_DEBUG_
  debug();
#endif

  concurrent_log();
  fuzzy_functional_test();

  test_parse_jepsen_etcd();
  test_jepsen_etcd();

#ifdef _ENABLE_EMBB_
  embb::base::Thread::SetThreadsMaxCount(255);

  embb_experiment(true);
  embb_experiment(false);
#endif

#ifdef _ENABLE_TBB_
  for (bool a : {true, false})
    tbb_functional_test(a);

  tbb_comprehensive_experiment(true);
  tbb_comprehensive_experiment(false);

  tbb_experiment(true);
  tbb_experiment(false);
#endif

  return 0;
}

