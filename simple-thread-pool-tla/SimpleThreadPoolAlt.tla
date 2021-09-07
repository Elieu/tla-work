---- MODULE SimpleThreadPoolAlt ----
EXTENDS SimpleThreadPool

CONSTANT 
    MaxOperations

ASSUME MaxOperations \in Nat

(*
 Applying this kind of constraints to a model will break the infinite/unbounded nature of a behavior, thus preventing 
 verification of any liveness properties (at least for TLC). We leave this constraint here for debug purpose only.
*)
OperationConstraint == \A x \in DOMAIN operationCounts: operationCounts[x] <= MaxOperations

_ShouldProducerStop(p) == operationCounts[p] >= MaxOperations
====