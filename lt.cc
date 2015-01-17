// Alex Horn, University of Oxford
//
// This source code gives an algorithm that uses ideas from SAT solvers
// to improve the state-of-the-art linearizability tester by Wing & Gong,
// including later extensions by Lowe:
//
//  http://www.cs.ox.ac.uk/people/gavin.lowe/LinearizabiltyTesting
//
// To build our source code, a C++11-compliant compiler is required.
// Our experiments use Intel's Threading Building Blocks (TBB) library.
#include <thread>
#include <mutex>
#include <atomic>
#include <condition_variable>
#include <tuple>
#include <memory>
#include <vector>
#include <climits>
#include <cstddef>
#include <utility>
#include <cassert>
#include <type_traits>
#include <unordered_set>

// functional testing and experiments
#include <random>
#include <functional>

// experiments
#include <chrono>
#include <iostream>

/// Allow users to print out counterexamples
#define _CLT_DEBUG_

#ifdef _CLT_DEBUG_
#include <string>
#include <ostream>
#include <sstream>
#include <algorithm>
#endif

#define _ENABLE_TBB_

#ifdef _ENABLE_TBB_
#include "tbb/concurrent_unordered_set.h"
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

/// Compositional and conflict-driven linearizability tester
namespace lt
{

template<class S>
class Entry;

/// Doubly-linked list of log entries

/// S - sequential data type
///
/// \remark not thread-safe
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
};

template<class S> class Entry;
template<class S> class Log;
template<class S> class ConcurrentLog;
template<class S> class Slicer;
template<class S, bool, bool> class LinearizabilityTester;
template<class S> class ParallelLinearizabilityTester;

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

#ifdef _CLT_DEBUG_
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

  virtual ~Op()
  {
    assert(ref_counter == 0);
  }

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

#ifdef _CLT_DEBUG_
  friend std::ostream& operator<<(std::ostream& os, const Op& op)
  {
    return op.print(os);
  }
#endif
};

class Bitset
{
public:
  typedef std::size_t Pos;

private:
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

  Blocks m_blocks;
  unsigned m_number_of_set_bits;

  Block& find_block(Pos pos)
  {
    BlockIndex i{block_index(pos)};
    assert(i < m_blocks.size());
    return m_blocks[i];
  }

public:
  Bitset(Pos max_pos)
  : m_blocks(blocks_size(max_pos)),
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

  std::size_t hash_code() const noexcept
  {
    std::size_t h{0};

    for (Block block : m_blocks)
      h ^= block;

    return h;
  }
};

struct BitsetHash
{
  std::size_t operator()(const Bitset& bitset) const noexcept
  {
    return bitset.hash_code();
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
  friend class LinearizabilityTester<S, true, true>;
  friend class LinearizabilityTester<S, true, false>;
  friend class LinearizabilityTester<S, false, true>;
  friend class LinearizabilityTester<S, false, false>;
  friend class ParallelLinearizabilityTester<S>;

  // Ref counted pointer because we need to copy logs so that we
  // can experimentally compare different linearizability testers
  //
  // However, this is an implementation detail and the strict type
  // of OpPtr<S> enforces at compile-time that we manage the
  // ownership of these kind of pointers on the user's behalf.
  Op<S>* m_op_ptr;
  unsigned m_entry_id;
  std::thread::id m_thread_id;
  EntryPtr<S> m_dependency;
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
    m_dependency{nullptr},
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
    m_dependency{nullptr},
    m_match{nullptr},
    m_is_call{false},
    prev{nullptr},
    next{nullptr} {}

  Entry(const Entry& entry)
  : m_op_ptr{entry.m_op_ptr},
    m_entry_id{entry.m_entry_id},
    m_thread_id{entry.m_thread_id},
    m_dependency{entry.m_dependency},
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
    m_dependency = entry.m_dependency;
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
    m_dependency = entry.m_dependency;
    m_match = entry.m_match;
    m_is_call = entry.m_is_call;
    prev = entry.prev;
    next = entry.next;

    entry.m_op_ptr = nullptr;
    entry.m_entry_id = 0;
    entry.m_thread_id = 0;
    entry.m_dependency = nullptr;
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

  EntryPtr<S> dependency() const noexcept
  {
    return m_dependency;
  }

  void set_dependency(EntryPtr<S> entry_ptr) noexcept
  {
    m_dependency = entry_ptr;
  }

  /// \pre: ret_entry_ptr->match() == nullptr
  /// \pre: not ret_entry_ptr->is_call()
  ///
  /// \post: this->is_call()
  /// \post: this == ret_entry_ptr->match()
  /// \post: this->match() == ret_entry_ptr
  /// \post: this->entry_id() == ret_entry_ptr->entry_id()
  /// \post: if this->is_partitionable(),
  ///        then this->op().partition() == ret_entry_ptr->op().partition()
  void set_match(EntryPtr<S> ret_entry_ptr) noexcept
  {
    assert(ret_entry_ptr->m_match == nullptr);
    assert(not ret_entry_ptr->is_call());

    ret_entry_ptr->m_match = this;
    ret_entry_ptr->op().m_is_partitionable = op().m_is_partitionable;
    ret_entry_ptr->op().m_partition = op().m_partition;
    ret_entry_ptr->set_entry_id(m_entry_id);

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

#ifdef _CLT_DEBUG_
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

#ifdef _CLT_DEBUG_
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
  friend class LinearizabilityTester<S, true, true>;
  friend class LinearizabilityTester<S, true, false>;
  friend class LinearizabilityTester<S, false, true>;
  friend class LinearizabilityTester<S, false, false>;
  friend class ParallelLinearizabilityTester<S>;

  bool m_is_linearizable;

#ifdef _CLT_DEBUG_
  unsigned m_cutoff_entry_id;
  EntryPtr<S> m_log_head_ptr;
#endif

public:
  /// Initially linearizable
  Result()
  : m_is_linearizable{true}
#ifdef _CLT_DEBUG_
    ,m_cutoff_entry_id{0U}
    ,m_log_head_ptr{nullptr}
#endif
  {}

  bool is_linearizable() const noexcept
  {
    return m_is_linearizable;
  }

#ifdef _CLT_DEBUG_
  /// \pre: not is_linearizable()
  void debug(std::ostream& os, bool verbose = false)
  {
    assert(not is_linearizable());

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

/// Asynchronous read-many/write-once Boolean flag
class InterruptFlag
{
private:
  static std::atomic<bool> s_flag;
  std::atomic<bool>* const m_flag_ptr;

public:
  InterruptFlag()
  : m_flag_ptr(&s_flag) {}

  /// Shared Boolean flag to signal threads to terminate
  InterruptFlag(std::atomic<bool>& atomic_flag)
  : m_flag_ptr(&atomic_flag) {}

  InterruptFlag(InterruptFlag& other)
  : m_flag_ptr(other.m_flag_ptr) {}

  /// Should be only set once by the main thread
  void set() noexcept
  {
    m_flag_ptr->store(true, std::memory_order_relaxed);
  }

  bool is_set() const noexcept
  {
    return m_flag_ptr->load(std::memory_order_relaxed);
  }
};

std::atomic<bool> InterruptFlag::s_flag(false);

namespace state
{
  /// Conflict analyzer for non-chronological backtracking

  /// A good conflict analyzer allows the LinearizabilityTester to
  /// perform non-chronological backtracking similar as in SAT solvers.
  /// In a nutshell, the idea behind non-chronological backtracking in
  /// the context of linearizability testing is as follows:
  ///
  /// Suppose we have an implementation of the concurrent "set" abstract
  /// data type (ADT) with the usual "remove" and "contains" operations.
  /// Let L be the following provisional linearization of some history:
  ///
  ///       remove(x) : success        contains(x) : found
  ///     |---------------------| L' |---------------------|
  ///
  /// where "x" is an item to be removed from the set and L' is some sub-
  /// linearization such that no operation in L' accesses item "x". Since
  /// the "remove(x)" operation succeeds but the subsequent "contains(x)"
  /// call supposedly finds "x", this linearization is invalid (it does
  /// not satisfy the specification of the set ADT). At this point,
  /// assuming there are no other entries that come next in the history
  /// after "contains(x)", the state-of-the-art WGL linearizability tester
  /// would now backtrack to the next possible entry in L' (if any). By
  /// assumption, however, there is no entry in L' which would make it
  /// possible for "contains(x)" to be linearized because "remove(x)"
  /// still precedes "contains(x)" in the stack of linearized entries.
  /// Our algorithm in LinearizabilityTester can recognize this with a
  /// suitable ConflictAnalyzer for the set ADT, thereby allowing it to
  /// directly backtracks to "remove(x)" instead.
  ///
  /// S - sequential data type
  template<class S>
  struct ConflictAnalyzer
  {
    /// Record the fact that entry_ptr has been linearized

    /// \pre: entry_ptr->is_call()
    /// \pre: entry_ptr->is_partitionable()
    void linearize(EntryPtr<S> entry_ptr);

    /// Undo previous linearize(entry_ptr)

    /// \pre: entry_ptr->is_call()
    /// \pre: entry_ptr->is_partitionable()
    void undo_linearize(EntryPtr<S> entry_ptr);

    /// Return entry pointer that conflicts with entry_ptr, or nullptr if none

    /// \pre: not entry_ptr->is_call()
    /// \pre: entry_ptr->is_partitionable()
    EntryPtr<S> analyze(EntryPtr<S> entry_ptr) const;
  };

  /// S - sequential data type
  template<class S>
  struct QuiescentConflictAnalyzer
  {
    void linearize(EntryPtr<S> entry_ptr)
    {
      assert(entry_ptr->is_call());
      assert(entry_ptr->is_partitionable());
    }

    void undo_linearize(EntryPtr<S> entry_ptr)
    {
      assert(entry_ptr->is_call());
      assert(entry_ptr->is_partitionable());
    }

    EntryPtr<S> analyze(EntryPtr<S> entry_ptr) const
    {
      assert(not entry_ptr->is_call());
      assert(entry_ptr->is_partitionable());

      return nullptr;
    }
  };
}

/// S - sequential data type
template<class S, bool enable_conflict_analyzer = true, bool enable_state_cache = true>
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

  // Statically enable/disable state caching
  typedef std::unordered_set<State, StateHash> EnabledStateCache;
  typedef std::nullptr_t DisabledStateCache;

  // Optionally memoize states

  // \remark for this, a good hash function is required
  typedef typename std::conditional<
    /* if */ enable_state_cache,
    /* then */ EnabledStateCache,
    /* else */ DisabledStateCache>::type StateCache;

  // Statically enable/disable conflict analyzer
  typedef typename std::conditional<
    /* if */ enable_conflict_analyzer,
    /* then */ state::ConflictAnalyzer<S>,
    /* else */ state::QuiescentConflictAnalyzer<S>>::type ConflictAnalyzer;

  // Maximum number of call/ret entries, i.e. half of the
  // total number of entry pointers reachable in m_log_head
  const std::size_t m_log_size;

  // History to linearize, every call is matched by a return
  const Entry<S> m_log_head;

  // Inter-thread termination signal
  InterruptFlag m_interrupt_flag;

  // Invariants:
  //
  // * for every EntryPtr<S> `e` in `m_calls`, `e->is_call()` holds
  // * for every EntryPtr<S> `e`, if `e` in `m_calls`, then `e` is not reachable
  //   from `m_log_head` by following the next pointers.
  Stack<S> m_calls;

  // Non-chronological backtracking information
  ConflictAnalyzer m_conflict_analyzer;

  // An approximation of the workload
  unsigned long m_number_of_iterations;

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

  // enable_state_cache is false
  static constexpr bool cache_state(const S& new_s, const EntryPtr<S>  entry_ptr,
    DisabledStateCache state_cache, Bitset& bitset)
  {
    return true;
  }

  // enable_state_cache is true
  static bool cache_state(const S& new_s, const EntryPtr<S>  entry_ptr,
    EnabledStateCache& state_cache, Bitset& bitset)
  {
    return std::get<1>(state_cache.emplace(bitset.immutable_set(entry_ptr->entry_id()), new_s));
  }

  /// Is history (i.e. every call/ret entry in the log) linearizable?
  bool is_linearizable(unsigned& global_linearized_entry_id)
  {
    S s, new_s;
    StateCache state_cache;
    bool is_entry_linearizable;
    EntryPtr<S> entry_ptr = m_log_head.next;

    // fixing the size is not merely an optimization but
    // necessary for checking the equality of bitsets
    Bitset linearized_entries(m_log_size);

    while (m_log_head.next != nullptr)
    {
      if (m_interrupt_flag.is_set())
        break;

      ++m_number_of_iterations;

      assert(entry_ptr != nullptr);
      if (entry_ptr->is_call())
      {
        assert(not m_calls.is_full());
        assert(entry_ptr->match() != nullptr);

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

          // if possible, keep track of linearized entries
          // in order to perform non-chronological backtracking
          if (entry_ptr->is_partitionable())
            m_conflict_analyzer.linearize(entry_ptr);

          // provisionally remove the entry from the history
          lift(entry_ptr);

          // restart from the beginning of the shortened history
          entry_ptr = m_log_head.next;
        }
        else // cannot linearize call entry
        {
          // get the next entry in the unmodified history
          entry_ptr = entry_ptr->next;

#ifdef _CLT_DEBUG_
          global_linearized_entry_id = std::max(global_linearized_entry_id, entry_ptr->entry_id());
#endif
        }
      }
      else // handle "return" entry
      {
        if (m_calls.is_empty())
          return false;

        EntryPtr<S> conflict_entry_ptr{nullptr};
        if (entry_ptr->is_partitionable())
          conflict_entry_ptr = m_conflict_analyzer.analyze(entry_ptr);

        EntryPtr<S> pop_entry_ptr;
        do
        {
          assert(not m_calls.is_empty());

          // revert state change
          std::tie(pop_entry_ptr, s) = m_calls.top();
          assert(pop_entry_ptr != nullptr);
          linearized_entries.reset(pop_entry_ptr->entry_id());

          if (pop_entry_ptr->is_partitionable())
            m_conflict_analyzer.undo_linearize(pop_entry_ptr);

          m_calls.pop();

          // undo the provisional linearization
          unlift(pop_entry_ptr);
        }
        while (conflict_entry_ptr != nullptr and pop_entry_ptr != conflict_entry_ptr);

        // continue after the entry to which we have just backtracked
        entry_ptr = pop_entry_ptr->next;
      }
    }

    assert(m_interrupt_flag.is_set() or m_calls.is_full());

    // all call entries have been linearized
    return true;
  }

public:
  LinearizabilityTester(LogInfo<S> log_info)
  : m_log_size{log_info.number_of_entries() >> 1},
    m_log_head{log_info.log_head_ptr()},
    m_interrupt_flag{},
    m_calls{m_log_size},
    m_conflict_analyzer{},
    m_number_of_iterations{} {}

  LinearizabilityTester(LogInfo<S> log_info,
    InterruptFlag& interrupt_flag)
  : m_log_size{log_info.number_of_entries() >> 1},
    m_log_head{log_info.log_head_ptr()},
    m_interrupt_flag{interrupt_flag},
    m_calls{m_log_size},
    m_conflict_analyzer{},
    m_number_of_iterations{} {}

  /// A rough approximation of the workload
  unsigned long number_of_iterations() const noexcept
  {
    return m_number_of_iterations;
  }

  bool is_linearizable()
  {
    unsigned disregard_cutoff_entry_id;
    return is_linearizable(disregard_cutoff_entry_id);
  }

  bool check(Result<S>& result)
  {
    bool r;

#ifdef _CLT_DEBUG_
    r = is_linearizable(result.m_cutoff_entry_id); 
    result.m_log_head_ptr = m_log_head.next;
#else
    r = is_linearizable();
#endif

    return result.m_is_linearizable = r;
  }
};

/// Coordinate the delivering of results and termination of threads

/// S - sequential data type
template<class S>
class Coordinator
{
private:
  unsigned m_number_of_threads;
  bool m_is_set;

  Result<S> m_result;
  std::mutex m_mutex;
  std::condition_variable m_cv;

  bool is_done() const noexcept
  {
    return m_is_set or m_number_of_threads == 0U;
  }

public:
  /// Coordinator expects `number_of_threads` to call goodbye()
  Coordinator(unsigned number_of_threads)
  : m_number_of_threads{number_of_threads},
    m_is_set{false},
    m_result{},
    m_mutex{},
    m_cv{} {}

  /// Must be called by every thread started by the coordinator
  void goodbye(const Result<S>& result)
  {
    bool is_set{false};
    unsigned number_of_threads;

    // unlock the mutex before notifying; otherwise, the
    // notified thread would unnecessarily block again
    {
      std::unique_lock<std::mutex> lock(m_mutex);
      assert(0U < m_number_of_threads);

      if (not (m_is_set or result.is_linearizable()))
      {
        m_result = result;
        m_is_set = is_set = true;
      }

      number_of_threads = --m_number_of_threads;
    }

    if (is_set or number_of_threads == 0U)
      m_cv.notify_one();
  }

  Result<S>& wait_for_result()
  {
    std::unique_lock<std::mutex> lock(m_mutex);
    m_cv.wait(lock, [this]{ return is_done(); });

    assert(is_done());
    return m_result;
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

/// A slicer partitions the history such that multiple threads can
/// independently check whether certain sub-histories are linearizable.
/// Our parallelization strategy hinges on Theorem 3.6.1 in "The Art of
/// Multiprocessor Programming" (Revised Ed.) by Herlihy and Shavit.
/// Our idea is also directly applicable to the known sequential
/// algorithms.
///
/// Typically only concurrent abstract data types such as sets and
/// hash tables are suitable for such a partitioning scheme.
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
  std::atomic<unsigned> m_current_partition;

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

    unsigned partition = m_current_partition.fetch_add(1U, std::memory_order_relaxed);
    if (partition < number_of_partitions)
      return m_sublogs[partition];

    return s_empty_log;
  }
};

/// S - sequential data type
template<class S>
class ParallelLinearizabilityTester
{
private:
  static void linearizability_tester(
    Slicer<S>& slicer,
    InterruptFlag& interrupt_flag,
    Coordinator<S>& coordinator)
  {
    Result<S> result;
    LogInfo<S> log_info{slicer.next_sublog_info()};
    while (not log_info.is_empty())
    {
      LinearizabilityTester<S> tester{log_info, interrupt_flag};
      tester.check(result);

      if (interrupt_flag.is_set() or not result.is_linearizable())
        break;

      log_info = slicer.next_sublog_info();
    }

    coordinator.goodbye(result);
  }

  const unsigned m_number_of_threads;
  Slicer<S> m_slicer;

public:
  /// Create as many threads as partitions
  ParallelLinearizabilityTester(LogInfo<S> log_info,
    unsigned number_of_partitions)
  : m_number_of_threads{number_of_partitions},
    m_slicer{log_info, number_of_partitions} {}

  ParallelLinearizabilityTester(LogInfo<S> log_info,
    unsigned number_of_partitions,
    unsigned number_of_threads)
  : m_number_of_threads{number_of_threads},
    m_slicer{log_info, number_of_partitions} {}

  bool is_linearizable()
  {
    Result<S> result;
    return check(result);
  }

  bool check(Result<S>& result)
  {
    std::atomic<bool> atomic_flag{false};
    InterruptFlag interrupt_flag{atomic_flag};
    Coordinator<S> coordinator{m_number_of_threads};
    std::vector<Thread> threads(m_number_of_threads);

    for (Thread& thread : threads)
      thread = Thread(
        linearizability_tester,
        std::ref(m_slicer),
        std::ref(interrupt_flag),
        std::ref(coordinator));

    result = coordinator.wait_for_result();
    interrupt_flag.set();

    for (Thread& thread : threads)
      thread.join();

    return result.is_linearizable();
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

template<class F, class ...Args>
void start_threads(unsigned number_of_threads, F&& f, Args&&... args)
{
  std::vector<Thread> threads(number_of_threads);

  for (Thread& thread : threads)
    thread = Thread(std::forward<F>(f), std::forward<Args>(args)...);

  for (Thread& thread : threads)
    thread.join();
}

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
    return m_bitset.hash_code();
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

#ifdef _CLT_DEBUG_
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

#ifdef _CLT_DEBUG_
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

#ifdef _CLT_DEBUG_
      std::ostream& print(std::ostream& os) const override
      {
        return os << op_name << "(" << std::to_string(value) << ")";
      }
#endif
    };
  }

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

  template<>
  class ConflictAnalyzer<Set>
  {
  private:
    std::vector<EntryPtr<Set>> m_backtrack_info;

    // post: partition < m_backtrack_info.size()
    void resize_vector_if_neccessary(unsigned partition)
    {
      if (m_backtrack_info.size() <= partition)
        m_backtrack_info.resize(partition + 1U);

      assert(partition < m_backtrack_info.size());
    }

  public:
    ConflictAnalyzer<Set>() : m_backtrack_info{} {}

    void linearize(EntryPtr<Set> entry_ptr)
    {
      assert(entry_ptr->is_call());
      assert(entry_ptr->is_partitionable());

      const unsigned partition{entry_ptr->op().partition()};
      resize_vector_if_neccessary(partition);

      EntryPtr<Set>& backtrack_entry_ptr = m_backtrack_info[partition];
      entry_ptr->set_dependency(backtrack_entry_ptr);
      backtrack_entry_ptr = entry_ptr;
    }

    void undo_linearize(EntryPtr<Set> entry_ptr)
    {
      assert(entry_ptr->is_call());
      assert(entry_ptr->is_partitionable());

      const unsigned partition{entry_ptr->op().partition()};
      if (partition < m_backtrack_info.size())
        m_backtrack_info[partition] = entry_ptr->dependency();

      entry_ptr->set_dependency(nullptr);
    }

    /// Return entry pointer for the last operation on the same datum, or null.
    EntryPtr<Set> analyze(EntryPtr<Set> entry_ptr) const
    {
      assert(not entry_ptr->is_call());
      assert(entry_ptr->is_partitionable());

      const unsigned partition{entry_ptr->op().partition()};
      assert(entry_ptr->op().partition() == entry_ptr->match()->op().partition());

      if (partition < m_backtrack_info.size())
        return m_backtrack_info[partition];

      return nullptr;
    }
  };
}

}

using namespace lt;

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

static void test_set()
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

static void test_set_op()
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

/// The empty log is trivially linearizable.
static void test_linearizability_empty_log()
{
  std::size_t number_of_entries{0U};
  LogInfo<state::Set> log_info;
  LinearizabilityTester<state::Set> t{log_info};
  assert(log_info.is_empty());
  assert(t.is_linearizable());
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
  assert(t.is_linearizable());
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
  assert(not t.is_linearizable());
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
  assert(t.is_linearizable() == (not ret));

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
  Result<state::Set> result;

  assert(t.check(result) == insert_ret);
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
  Result<state::Set> result;
  assert(t.check(result) == insert_ret);
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
  Result<state::Set> result;
  assert(t.check(result) == insert_ret);
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
  Result<state::Set> result;

  assert(t.check(result) == insert_ret);
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
  Result<state::Set> result;

  assert(t.check(result) == (insert_ret and contains_ret));
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
  Result<state::Set> result;

  assert(t.check(result) == (insert_ret and not contains_ret));
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
  Result<state::Set> result;

  assert(t.check(result) == (not (insert_ret_0 == insert_ret_1)));
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
  Result<state::Set> result;

  assert(t.check(result) == (insert_ret_0 and not insert_ret_1));
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
  Result<state::Set> result;
  assert(not t.check(result));
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
  Result<state::Set> result;

  assert(not t.check(result));
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
  Result<state::Set> result;
  assert(not t.check(result));
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
  assert(t.is_linearizable());
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
  assert(t.is_linearizable());
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
  assert(t.is_linearizable());
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

  Result<state::Set> result;
  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check(result));
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

  Result<state::Set> result;
  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check(result));
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

  Result<state::Set> result;
  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check(result));
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

  Result<state::Set> result;
  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check(result));
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

  Result<state::Set> result;
  LinearizabilityTester<state::Set> t{log.info()};
  assert(not t.check(result));
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

  Result<state::Set> result;
  LinearizabilityTester<state::Set> t{log.info()};
  assert(t.check(result) == insert_ret);
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
  assert(tester_0.is_linearizable());

  LinearizabilityTester<state::Set> tester_1{slicer.sublog_info(y)};
  assert(tester_1.is_linearizable());
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
  assert(not tester_0.is_linearizable());

  LinearizabilityTester<state::Set> tester_1{slicer.sublog_info(y)};
  assert(tester_1.is_linearizable());
}

// Since every sub-history is linearizable, the entire history is linearizable:

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
static void parallel_linearizability_tester_000()
{
  constexpr unsigned number_of_partitions = 2U;

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

  Result<state::Set> result;
  ParallelLinearizabilityTester<state::Set> t{log.info(), number_of_partitions};
  assert(t.check(result));
}

// Since every sub-history is linearizable, the entire history is linearizable:
//
// Let x = '\0' and y = '\1'.
//
//   insert(x) : true
// |------------------|
//
//      contains(y) : false
//    |---------------------|
//
//         contains(x) : false
//       |---------------------|
static void parallel_linearizability_tester_001()
{
  constexpr unsigned number_of_partitions = 2U;

  constexpr char x = '\0';
  constexpr char y = '\1';

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

  Result<state::Set> result;
  ParallelLinearizabilityTester<state::Set> t{log.info(), number_of_partitions};
  assert(t.check(result));
}

// Since the sub-history of x is not linearizable, the entire history is not linearizable:
//
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
static void parallel_linearizability_tester_002()
{
  constexpr unsigned number_of_partitions = 2U;

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

  Result<state::Set> result;
  ParallelLinearizabilityTester<state::Set> t{log.info(), number_of_partitions};
  assert(not t.check(result));
  assert(not result.is_linearizable());
}

#ifdef _CLT_DEBUG_

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

  assert(not t.check(result));

  std::stringstream os;
  result.debug(os);

  assert(os.str() == "entry id: 0, thread id: " INIT_THREAD_ID ", call: contains(1)\n"
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

  Result<state::Set> result;
  ParallelLinearizabilityTester<state::Set> t{log.info(), 1U};
  assert(not t.check(result));
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

  const unsigned number_of_partitions{worker_configuration.max_value + 1U};
  ParallelLinearizabilityTester<state::Set> tester{concurrent_log.info(), number_of_partitions};

  Result<state::Set> result;
  assert(not tester.check(result));
}

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

static void tbb_functional_test(bool use_parallel, bool is_linearizable)
{
  constexpr unsigned number_of_threads = 4U;
  constexpr WorkerConfiguration worker_configuration = {'\27', 1000U};
  constexpr unsigned log_size = number_of_threads * worker_configuration.number_of_ops;

  ConcurrentLog<state::Set> concurrent_log{2U * log_size};
  tbb::concurrent_unordered_set<char> concurrent_set;

  if (not is_linearizable)
  {
    auto pair = concurrent_set.insert(5);
    assert(pair.second);
  }

  if (use_parallel)
  {
    // create history
    start_threads(number_of_threads, tbb_comprehensive_worker, std::cref(worker_configuration),
      std::ref(concurrent_log), std::ref(concurrent_set));

    constexpr unsigned number_of_partitions{worker_configuration.max_value + 1U};
    ParallelLinearizabilityTester<state::Set> tester{concurrent_log.info(), number_of_partitions};
    assert(tester.is_linearizable() == is_linearizable);
  }
  else
  {
    // create history
    start_threads(number_of_threads, tbb_worker, std::cref(worker_configuration),
      std::ref(concurrent_log), std::ref(concurrent_set));

    LinearizabilityTester<state::Set> tester{concurrent_log.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
}

static void tbb_experiment(bool is_linearizable)
{
  constexpr unsigned number_of_threads = 4U;
  constexpr WorkerConfiguration worker_configuration = {'\27', 10000U};
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

  const LogInfo<state::Set> log_info{concurrent_log.info()};
  // std::cout << log_info << std::endl;

  auto start = std::chrono::system_clock::now();
  auto end = std::chrono::system_clock::now();
  std::chrono::seconds seconds;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, false, true> tester{log_copy.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, enabled state cache: " << seconds.count() << " s" << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, false, false> tester{log_copy.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, disabled state cache: " << seconds.count() << " s" << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, true, true> tester{log_copy.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Conflict-driven, enabled state cache: " << seconds.count() << " s" << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, true, false> tester{log_copy.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Conflict-driven, disabled state cache: " << seconds.count() << " s" << std::endl;
}

/// Run as many different kinds of linearizability testers as possible
static void tbb_comprehensive_experiment(bool is_linearizable)
{
  constexpr unsigned number_of_threads = 4U;
  constexpr WorkerConfiguration worker_configuration = {'\27', 10000U};
  constexpr unsigned log_size = number_of_threads * worker_configuration.number_of_ops;

  std::cout << "tbb_comprehensive_experiment : " << (is_linearizable ? "" : "not ") << "linearizable" << std::endl;

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
    LinearizabilityTester<state::Set, false, true> tester{log_copy.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, enabled state cache: " << seconds.count() << " s" << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, false, false> tester{log_copy.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Baseline, disabled state cache: " << seconds.count() << " s" << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, true, true> tester{log_copy.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Conflict-driven, enabled state cache: " << seconds.count() << " s" << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    LinearizabilityTester<state::Set, true, false> tester{log_copy.info()};
    assert(tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Conflict-driven, disabled state cache: " << seconds.count() << " s" << std::endl;

  const unsigned number_of_partitions{worker_configuration.max_value + 1U};

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    Slicer<state::Set> slicer{log_copy.info(), number_of_partitions};
    bool r{true};
    for (unsigned partition = 0; partition < slicer.number_of_partitions; ++partition)
    {
      LinearizabilityTester<state::Set> tester{slicer.sublog_info(partition)};
      if (not tester.is_linearizable())
      {
        r = false;
        break;
      }
    }
    assert(r == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Compositional: " << seconds.count() << " s" << std::endl;

  start = std::chrono::system_clock::now();
  {
    Log<state::Set> log_copy{log_info};
    ParallelLinearizabilityTester<state::Set> parallel_tester{log_copy.info(), number_of_partitions, number_of_threads};
    assert(parallel_tester.is_linearizable() == is_linearizable);
  }
  end = std::chrono::system_clock::now();
  seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  std::cout << "Parallel: " << seconds.count() << " s" << std::endl;
}
#endif

int main()
{
  test_stack();
  test_set();
  test_bitset();
  test_set_op();

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
      }

  test_slice_000();
  test_slice_001();

  parallel_linearizability_tester_000();
  parallel_linearizability_tester_001();
  parallel_linearizability_tester_002();

#ifdef _CLT_DEBUG_
  debug();
#endif

  concurrent_log();
  fuzzy_functional_test();

#ifdef _ENABLE_TBB_
  for (bool a : {true, false})
    for (bool b : {true, false})
      tbb_functional_test(a, b);

  tbb_comprehensive_experiment(true);
  tbb_comprehensive_experiment(false);

  tbb_experiment(true);
  tbb_experiment(false);
#endif

  return 0;
}

