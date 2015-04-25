# Linearizability checker

[Linearizability][linearizability] is a well-established correctness criterion for
concurrent data types and it corresponds to one of the [three desirable properties][CAP]
of a distributed system, namely <em>consistency</em>. The intuition behind linearizability
is that all operations in a so-called <em>history</em> can be reordered along a timeline such
that a given sequential specification holds. Given a history and sequential specification,
a <em>linearizability checker</em> checks whether such a reordering exists.

In general, checking linearizability is [NP-complete][NP-complete] and so writing an
efficient linearizability checker is inherently difficult. This is motivation to
experimentally compare various techniques to find out what works well in practice -
the purpose of this source code repository.

For our experiments, we collected histories from Intel's [Threading Building Blocks][TBB]
(TBB) library, Siemens's [Embedded Multicore Building Blocks][EMBB] (EMBB) library, and
the distributed key-value store [etcd][etcd] using [Jepsen][Jepsen].

In a nutshell, the result of our work is a linearizability checker that can check CP
distributed systems on which current implementations timeout or run out of memory.

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

where the read returns the last written register value, namely 2. By contrast, the
following history `H'` is non-linearizable because there is no valid reordering of
reads and writes that satisfies the expected behaviour of a register:

```
          write(1)        read() : 2      
        |----------|    |------------|

                                           write(2)
                                         |----------|
```

## Related work 

A detailed discussion of related work is given in our [FORTE'15 paper][HK2015].
Here, we only mention that there has been surprisingly little work done in
systematically evaluating and comparing possible linearizability algorithms,
the various ways they can be implemented, or trying out ideas from the SAT
solver community.

## Results

We published the most relevant experimental results in [FORTE'15][HK2015].
Under the assumption of so-called <em>P</em>-compositionality, we show that
our technique improves [Lowe's state-of-the-art linearizability checker][L2014]
by one order of magnitude, in space and/or time.

This repository gives the source code that is required for all the experiments,
including additional ones that we did not discuss in the paper due to space.
To compile our source code, a C++11-compliant compiler is required.

To repeat our experiments with [Lowe's concurrent set implementations][L2014],
run the following command:

    $ make hashset-test

In addition, by downloading, compiling and configuring TBB and EMBB in the
[Makefile][Makefile], you will also be able to run the other experiments.

You may be also interested in running experiments with [etcd 2.0][etcd]
which we did not have space to discuss in the paper:

    $ make etcd-test 

This runs our tool against 100 collected etcd histories, and completes in a few
seconds. By contrast, [Knossos][Knossos] times out on benchmark 7 and 99, and
runs out of memory on 40, 57, 85 and 97 (all benchmarks can be found in the
[jepsen directory][jepsen-benchmarks]). Note that the failures in etcd are
expected here because we allow read requests to bypass the consensus protocol
(by setting `quorum=false`)! As a sanity check, we have also tried three tests
with `quorum=true' and we did not find any linearizability bugs.

## Conclusion

We have implemented a new linearizability checker that we evaluated through
extensive experiments on [TBB][TBB], [EMBB][EMBB] and [etcd][etcd]. We found
that our linearizability checker can solve instances on which current implementations
timeout or run out of memory.

Of course, there are always things to improve, and we warmly invite any form of feedback,
questions etc. We also welcome patches (including benchmarks) as Github pull requests.

[CAP]: http://en.wikipedia.org/wiki/CAP_theorem
[linearizability]: http://dl.acm.org/citation.cfm?id=78972
[NP-complete]: http://en.wikipedia.org/wiki/NP-complete

[L2014]: http://www.cs.ox.ac.uk/people/gavin.lowe/LinearizabiltyTesting/
[HK2015]: http://arxiv.org/abs/1504.00204

[etcd]: https://github.com/coreos/etcd
[TBB]: https://www.threadingbuildingblocks.org/
[EMBB]: https://github.com/siemens/embb
[Knossos]: https://github.com/aphyr/knossos
[Jepsen]: https://github.com/aphyr/jepsen
[Makefile]: https://github.com/ahorn/linearizability-checker/blob/master/Makefile
[jepsen-benchmarks]: https://github.com/ahorn/linearizability-checker/tree/master/jepsen
