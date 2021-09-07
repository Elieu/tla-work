# A Collection of Specifications about the Implementation of A Simple Thread Pool

## Prerequisites

- If you never heard of the first-order predicate logic or set theory, you should probably go to the reading list at the end of this document first.

- If you felt confused about any terminology in either this document or the source code, you should probably refer to the reading list at the end of this document first.

- If you never read Leslie Lamport's foundational paper: _Time, Clocks and the Ordering of Events in a Distributed System. Leslie Lamport. Communications of the ACM 21, 7 (July 1978), 558-565._, you should probably read it carefully first, and make sure that you truly understand the representation of distributed computation model.

## Introductions

This repository contains a collection of TLA+ specifications formally describing the implementation of a simple thread pool along with its dependencies. These specifications also draw some conclusions about the correctness of the underlying model, which are roughly divided into safety properties and liveness properties. All the specifications and the corresponding properties are ready to be verified by the TLC model checker.

All models in this repository are specified completely in native TLA+ language instead of PlusCal, which means that you don't need a translation before simulating the models.

## Motivations

The motivation for creating such an implementation came from the requirement that we need a thread pool (implemented in Java) which provides some kind of guarantees for task execution order. More specifically, we attached a key to each task submitted to a thread pool, and require that all tasks with the same key should be executed and completed in the same order as their submissions.

This thread pool is intended to be used in a high-throughput scenario, which means that performance is critical.

- Firstly, all blocking queue based implementations fall out of consideration, since the blocking of a caller is unacceptable.

- Secondly, the desired implementation should be lock-free, since the frequency of task submission is expected to be rather high and any unnecessary context switch is unacceptable.

The most matched (but by no means satisfied) implementation in Java standard library (at this writing, Java 16) seems to be Doug Lea's `ForkJoinPool`. But unfortunately, `ForkJoinPool` is based on randomization and work stealing which provide almost no guarantees about order. After some initial investigation, we finally gave up seeking for an existing implementation which is expected to be both reliable enough and easy for extension. On the contrary, we decided to create an our own implementation which should not be too hard.

At last, a working implementation has been built (`OrderedThreadPool`), without too many difficulties. At this point, we still need to verify that our implementation is correct using some formal way. As we know that verifying the correctness of a concurrent/distributed algorithm is extremely difficult (if not impossible), since there are too many (or even infinite) possibilities of executions (transitions of states). Unit test is absolutely not going to work in this case, since it is not able to simulate all race conditions. In the end, we decides to resort to TLA+, resulting the specifications in this repository.

## Source File Organizations

- `SimpleThreadPool.tla`: This module is the main specification of the thread pool implementation. This module is meant to be a general/abstract model without any artificially introduced constraints or limitations. This module can not be directly checked by TLC, refer to the corresponding extension `SimpleThreadPoolAlt.tla` instead.

- `ProcessControll.tla`: This module is the dependency of `SimpleThreadPool.tla`, aiming to provide some general process related manipulations. Refer to the comments inside for more details. This module is ready to be verified by TLC.

- `SimpleThreadPoolAlt.tla`: This module is a simple extension of `SimpleThreadPool.tla`, providing the concrete implementation of some abstract operator. This module is ready to be verified by TLC.

- `*.cfg`: These are the configuration files for corresponding models, required by TLC.

## Model Simulation and Verification

There are two modules which are ready to be checked by TLC, namely `SimpleThreadPoolAlt.tla` and `ProcessControll.tla` (together with corresponding `.cfg` files). Provide the module specification and configuration file to TLC in order to start a simulation/verification.

The default configuration file usually limits the model to a relatively small scale (producer count, consumer count, max operation count, etc.) which is quite suitable for debugging and development. Be aware that increasing this scale will dramatically increase the time consumption for model verification, especially when all liveness properties are required to be checked. More over, the hardware resource (especially memory capacity) limitations might even not support to verify a large model. Defining a small model and disabling (comment them out in configuration file) some liveness properties checking are usually good choices for a quick start.

## Further Readings and Recommendations about TLA+

- Leslie Lamport's _Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers_.

  This book is obviously the first choice, since no one knows TLA+ better than its creator. This book focuses on native TLA+ only.

- _Practical TLA+: Planning Driven Development_ from Apress publisher.

  This book is also a good choice for beginners especially programmer, but focusing on PlusCal instead. One should always try to start with and stick with native TLA+. Keep in mind that in order to represent a real complex model with maximum freedom, you should always embrace native TLA+. Try to think like a mathematician instead of a programmer.
