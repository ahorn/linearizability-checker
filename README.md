# Linearizability tester

Brewer's [CAP theorem][CAP] states that any distributed system can satisfy at most two
of the following desirable properties: consistency (C), availability (A) and partition
tolerance (P). Crucially, the "C" in "CAP" is identical to the well-known concept of
[linearizability][linearizability]. The intuition behind linearizability is that all
operations in a so-called <em>history</em> can be reordered along a timeline such that
a given sequential specification holds. So given a history and sequential specification,
a <em>linearizability tester</em> checks whether there exists such a reordering.

In general, checking linearizability is [NP-complete][NP-complete]. Given the high
computational complexity of this problem, writing an efficient linearizability tester
is a difficult task. This is motivation to experimentally compare various techniques,
and find a combination of techniques that works well in practice. This source code
repository shows the humble beginnings of such an endeavour, and we welcome people
to join the discussion and bounce off ideas. It's a hard problem , and therefore
should be fun to work on!

## Example

Consider the following history `H` of read and write operations on a register:

```
          write(1)        read() : 2      
        |----------|    |------------|

                        write(2)
                      |----------|
```

The `write(1)` happens-before the two remaining `read()` and `write(2)` operations.
Note that `read()` and `write(2)` happen concurrently because neither finishes before
the other. Then `H` is linearizable because the operations can be reordered as follows:

        write(1); write(2); read()

where the read returns the last written register value, namely 2. In contrast, the
following history `H'` is non-linearizable because there is no valid reordering of
reads and writes that satisfies the expected behaviour of a register:

```
          write(1)        read() : 2      
        |----------|    |------------|

                                           write(2)
                                         |----------|
```

## Related work 

The first linearizability algorithm was published by [Wing and Gong][WG1993]. Most
recently, [Lowe][L2014] has extended their algorithm with a form of state caching
and described a new algorithm altogether. Independently, [Kingsbury][K2014] showed
how symmetry reduction and parallelization techniques can be successfully used to
disprove linearizability of real-world distributed systems such as [etcd][etcd].

To date, however, there has been surprisingly little work done in systematically
evaluating and comparing possible linearizability algorithms, the various ways
they can be implemented, or trying out ideas from the SAT solver community.

## Experiments

We setup experiments in which we looked at things like hashing, non-chronological
backtracking, partitioning schemes and parallelization. For our experiments, we
collected histories from three sources: Intel's [Threading Building Blocks][TBB] (TBB)
library, Siemens's [Embedded Multicore Building Blocks][EMBB] (EMBB) library, and the
[etcd][etcd] distributed key-value store (collected via [Jepsen][Jepsen]).

Based on these experiments, this repository gives the source code of a tool that
combines the techniques we have found so far to be most effective. To compile
our source code, a C++11-compliant compiler is required. For example,

    $ make etcd-test 

compiles and then runs our tool against the collected etcd histories. This completes
in a few seconds, whereas [Knossos][Knossos] would take a couple of hours.

In summary, the results of our work look promising and we warmly invite any feedback
or patches that can further advance the field.

[CAP]: http://en.wikipedia.org/wiki/CAP_theorem
[linearizability]: http://dl.acm.org/citation.cfm?id=78972
[NP-complete]: http://en.wikipedia.org/wiki/NP-complete

[WG1993]: http://dl.acm.org/citation.cfm?id=163525
[L2014]: http://www.cs.ox.ac.uk/people/gavin.lowe/LinearizabiltyTesting/
[K2014]: https://aphyr.com/posts/314-computational-techniques-in-knossos

[etcd]: https://github.com/coreos/etcd
[TBB]: https://www.threadingbuildingblocks.org/
[EMBB]: https://github.com/siemens/embb
[Knossos]: https://github.com/aphyr/knossos
[Jepsen]: https://github.com/aphyr/jepsen
