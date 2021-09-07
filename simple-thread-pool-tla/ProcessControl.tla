---- MODULE ProcessControl ----

(*
 This module contains a simulation of the "LockSupport" mechanism in JDK-11. Refer to the corresponding Java doc for 
 more detailed information. In addition, this module is extended to simulate the process termination behavior which is 
 intended to simplify processes related manipulation.

 About the terminology:
 Strictly speaking, the "LockSupport" mechanism in JDK-11 operates on threads instead of processes. Actually, some OS, 
 e.g. Linux, even chooses to implement thread on top of process (light-weight). But, keep in mind that we/TLA are 
 talking about some model/system with a high level abstraction which does not bound to a specific programming language 
 or a particular OS. The boundary of thread and process is often quite obscure under those circumstances. For example, 
 almost all OSes provides some kind of mechanism to share memory among processes, thus allowing lock-free programming 
 even between processes. For another example, many traditional inter-thread lock-based synchronization data structures 
 have their inter-process equivalences, such as lock/semaphore. Due to the above reasons, we use the two terms (thread 
 and process) inter-changeably unless explicitly specified. In most circumstances, we prefer the term "process", since 
 it is the convention in existing distributed system related literatures.
*)

EXTENDS TLC

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANT 
    (* set of IDs for all managed processes *)
    Processes

(*
 Theoretically, we are able to operate on infinite sets, but that makes no sense in practice. In addition, it might 
 introduce unnecessary difficulties to TLC when checking some kind of properties.
*)
ASSUME IsFiniteSet(Processes)
ASSUME Cardinality(Processes) > 0

VARIABLE 
    (* a per-process status indicating whether a processing is in a running/active state *)
    activeStatuses,
    (* a per-process status indicating whether the next park operation should return immediately with no blocking *)
    permits,
    (* a per-process status indicating whether a process is terminated *)
    terminationStatuses

LOCAL vars == <<activeStatuses, permits, terminationStatuses>>
----
(* This is the set of all non-terminated processes that are in the running state. *)
ActiveProcesses == {p \in Processes: activeStatuses[p] = TRUE /\ terminationStatuses[p] = FALSE}

(* This is the set of all non-terminated processes that are in the blocked/inactive state. *)
BlockedProcesses == {p \in Processes: activeStatuses[p] = FALSE /\ terminationStatuses[p] = FALSE}

(* This is the set of all terminated processes. *)
TerminatedProcesses == {p \in Processes: terminationStatuses[p] = TRUE}

LOCAL AssertValidProcess(p) == Assert(p \in Processes, "Trying to operate an invalid process.")

LOCAL AssertProcessActive(p) == 
    /\ AssertValidProcess(p) 
    /\ Assert(p \in ActiveProcesses, "Trying to operate an inactive process.")

Park(p) == 
    (* Practically, an inactive process is unable to park itself, since there is no such an API. *)
    AssertProcessActive(p) /\
    /\ permits' = [permits EXCEPT ![p] = FALSE]
    /\ activeStatuses' = [activeStatuses EXCEPT ![p] = IF permits[p] = FALSE THEN FALSE ELSE TRUE]
    /\ UNCHANGED terminationStatuses

Unpark(p) == 
    (* Unparking a terminated process has no practical meaning, but let's allow it since the API does not forbid it. *)
    AssertValidProcess(p) /\
    LET _isActive == p \in ActiveProcesses IN 
    \/ /\ ~_isActive
       /\ permits' = [permits EXCEPT ![p] = TRUE]
       /\ activeStatuses' = [activeStatuses EXCEPT ![p] = TRUE]
       /\ UNCHANGED terminationStatuses
    \/ /\ _isActive
       /\ permits' = [permits EXCEPT ![p] = TRUE]
       /\ UNCHANGED <<activeStatuses, terminationStatuses>>

Terminate(p) ==
    (* Practically, an already terminated process is unable to actively terminated again. *)
    AssertProcessActive(p) /\
    /\ terminationStatuses' = [terminationStatuses EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<activeStatuses, permits>>
----
Init == 
    /\ activeStatuses = [p \in Processes |-> TRUE]
    /\ permits = [p \in Processes |-> FALSE]
    /\ terminationStatuses = [p \in Processes |-> FALSE]

LOCAL ParkAProcess == \E p \in Processes: 
    /\ p \in ActiveProcesses
    /\ Park(p)

LOCAL UnparkAProcess == \E p \in Processes: 
    /\ p \notin TerminatedProcesses
    /\ Unpark(p)

LOCAL TerminateAProcess == \E p \in Processes:
    /\ p \in ActiveProcesses
    /\ Terminate(p)

LOCAL Next == 
    \/ ParkAProcess
    \/ UnparkAProcess
    \/ TerminateAProcess
    \/ /\ TerminatedProcesses = Processes
       /\ UNCHANGED vars

LOCAL Liveness ==
    /\ WF_vars(ParkAProcess)
    /\ WF_vars(UnparkAProcess)
    /\ WF_vars(TerminateAProcess)

LOCAL Spec == Init /\ [][Next]_vars /\ Liveness
----
(* Type Invariant *)
LOCAL TypeInv == 
    /\ DOMAIN activeStatuses = Processes
    /\ DOMAIN permits = Processes
    /\ DOMAIN terminationStatuses = Processes
    /\ \A p \in Processes: 
        /\ activeStatuses[p] \in BOOLEAN
        /\ permits[p] \in BOOLEAN 
        /\ terminationStatuses[p] \in BOOLEAN 

THEOREM Spec => []TypeInv
----
(* This section focuses on basic safety properties: *)

(* Any inactive process should not have permits. *)
LOCAL InactiveProcessHasNoPermit == 
    \A p \in Processes: activeStatuses[p] = FALSE => permits[p] = FALSE

(* Any active or blocked process is non-terminated. *)
LOCAL ActiveAndBlockedProcessesAreNonTerminated == 
    /\ ActiveProcesses \cap TerminatedProcesses = {}
    /\ BlockedProcesses \cap TerminatedProcesses = {}

(* Any non-terminated process is either active or blocked. *)
LOCAL NonTerminatedProcessIsEitherActiveOrBlocked == 
    /\ {p \in Processes: p \notin TerminatedProcesses} = ActiveProcesses \cup BlockedProcesses
    /\ ActiveProcesses \cap BlockedProcesses = {}

THEOREM Spec =>
    /\ []InactiveProcessHasNoPermit
    /\ []ActiveAndBlockedProcessesAreNonTerminated
    /\ []NonTerminatedProcessIsEitherActiveOrBlocked
----
(* This section focuses on liveness properties: *)

(* 
 The termination of a process leads to eventually always termination of that process.

 Actually, this property might be stronger, such as: a terminated process never come back alive in any single instant. 
 But I have no idea about how to express that using currently supported temporal formulas.
*)
LOCAL TerminationLeadsToEventuallyAlwayTermination == \A p \in Processes:
    (p \in TerminatedProcesses) ~> <>[](p \in TerminatedProcesses)

THEOREM Spec => TerminationLeadsToEventuallyAlwayTermination
====
