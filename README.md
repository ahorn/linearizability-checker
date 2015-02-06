# Linearizability tester

Brewer's [CAP theorem][CAP] states that any distributed system can satisfy at most two
of the following desirable properties: consistency (C), availability (A) and partition
tolerance (P). Crucially, the "C" in "CAP" is identical to the well-known concept of
[linearizability][linearizability]. The intuition behind linearizability is that all
operations in a so-called <em>history</em> can be reordered along a timeline such that
a given sequential specification holds. Given a history and sequential specification,
a <em>linearizability tester</em> checks whether there exists such a reordering.

In general, checking linearizability is [NP-complete][NP-complete] and so writing an
efficient linearizability tester is inherently difficult. This is motivation to
experimentally compare various techniques to find out what works well in practice -
the thrust behind this source code repository.

For our experiments, we collected histories from Intel's [Threading Building Blocks][TBB]
(TBB) library, Siemens's [Embedded Multicore Building Blocks][EMBB] (EMBB) library, and
the distributed key-value store [etcd][etcd] using [Jepsen][Jepsen]. The result of our
work is a linearizability tester that can check CP distributed systems on which current
implementations timeout or run out of memory.

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

## Results

This repository gives the source code of a tool that combines techniques that we
found to be most effective in checking linearizability. To compile our source code,
a C++11-compliant compiler is required. To repeat our experiments with [etcd][etcd]
run the following command:

    $ make etcd-test 

This runs our tool against 100 collected etcd histories, and completes in a few
seconds. In contrast, [Knossos][Knossos] times out on benchmark 7 and 99, and
runs out of memory on 40, 57, 85 and 97 (all benchmarks can be found in the
[jepsen directory][jepsen-benchmarks]).

And our experiments with [Lowe's concurrent hashset implementations][L2014] can
be run via:

    $ make hashset-test

Our tool is one order of magnitude faster than [Lowe's linearizability tester][L2014].

In addition, by downloading, compiling and configuring TBB and EMBB in the
[Makefile][Makefile], you will also be able to run the other experiments. More
details on those experiments can be found [here][H2015-group-talk].

## Conclusion

We have implemented a new linearizability tester that combines insights from the
literature with quantitative data collected through extensive experiments on [TBB][TBB],
[EMBB][EMBB] and [etcd][etcd]. Our linearizability tester can solve instances on
which current implementations timeout or run out of memory. Of course, there are
always things to improve, and we warmly invite any form of feedback, questions etc.
We also welcome patches (including benchmarks) as Github pull requests.

[CAP]: http://en.wikipedia.org/wiki/CAP_theorem
[linearizability]: http://dl.acm.org/citation.cfm?id=78972
[NP-complete]: http://en.wikipedia.org/wiki/NP-complete

[WG1993]: http://dl.acm.org/citation.cfm?id=163525
[L2014]: http://www.cs.ox.ac.uk/people/gavin.lowe/LinearizabiltyTesting/
[K2014]: https://aphyr.com/posts/314-computational-techniques-in-knossos
[H2015-group-talk]: https://www.cs.ox.ac.uk/people/alex.horn/linearizability-tester-group-talk-2015-02-05.pdf

[etcd]: https://github.com/coreos/etcd
[TBB]: https://www.threadingbuildingblocks.org/
[EMBB]: https://github.com/siemens/embb
[Knossos]: https://github.com/aphyr/knossos
[Jepsen]: https://github.com/aphyr/jepsen
[Makefile]: https://github.com/ahorn/linearizability-tester/blob/master/Makefile
[jepsen-benchmarks]: https://github.com/ahorn/linearizability-tester/tree/master/jepsen
