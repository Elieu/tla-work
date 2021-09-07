---- MODULE SimpleThreadPool ----

(*
 This module specifies the implementation of a simple thread pool with fixed on-demand worker threads and per-worker 
 unbounded task queues. In this model, there are several pre-determined producers and consumers: producer generates 
 tasks and put them in task queues while each consumer is responsible for retrieving tasks from its own task queue and 
 execute them. In practice, producer is effectively the caller thread, while the consumer is the worker thread. In this 
 specification, the terms producer/caller and consumer/worker are used interchangeably, but we prefer producer and 
 consumer in most scenarios.

 The producers are modeled as a collection of pre-determined processes. Theses processes are conceptually always active 
 and never terminated. But there is some abstract stop condition (refer to ShouldProducerStop(_)) that controls when a 
 producer should stop performing any operations further. It is also fine for this stop condition to be never set. In 
 this case, one is trying to simulate a system with infinite states and will never terminate. Currently, there are two 
 supported operations for a producer: 1) Submit a task to the thread pool; 2) Shutdown the thread pool. Those are 
 exactly the public APIs provided by the thread pool.

 The consumers are modeled as a collection of pre-determined processes. But unlike a producer, a consumer is able to 
 either block (become inactive) or terminate (be come terminated) itself, thus a consumer is always in one of the 
 following states: active, inactive and terminated. While a consumer is inactive, it is the producer's responsibility 
 to unblock it thus brings it active again. Although all allowed consumers are pre-determined, consumer's creation is 
 modeled as an on-demand fashion, i.e. lazy initialization in software engineering. Once a consumer becomes terminated, 
 it remains terminated from then on. All consumers are running the same deterministic logic on their own.

 The atomicity of process operation is naturally modeled as an action/step in TLA+, while the continuation of process 
 operation is modeled as context switches similar to a physical machine. All process (either producer or consumer) 
 operations are further divided into a series of actions corresponding to TLA+'s state transitions. Those actions should
 be considered to be un-dividable, thus determining the granularity of the high level operations. A context record is 
 constructed for each process, storing necessary information in order to enable an "execution flow" to temporally leave 
 and then come back later. The functionality of this context record is quite similar to a process stack in a physical 
 machine. It is the action's responsibility to ensure that the context information is properly stored and to determine 
 how to continue an possible on-going operation. A process should never try to access the context records of others. 
 Each process determines what to carry out based on current context record, while the scheduler determines which process 
 to run next.

 The process scheduler is naturally modeled as the top level state transition logic of the main specification. The 
 process scheduler choose which process to run next based on various information, such as: process state, context 
 record, stop condition, etc. Note that there is no entity called scheduler defined in this specification. Instead, the 
 process scheduler is implicitly encoded into the top level actions. In this way, the fairness of the process scheduler 
 is then naturally mapped to the fairness of TLA+'s liveness properties.

 Other notes:

 1) The execution of a submitted task is not modeled in this specification, and there is even no concrete representation 
 of tasks. This is fine since the actual execution of the task or even the atomicity of the task is not going to affect 
 the correctness of the model in this specification. Another way of saying this is that the task execution is irrelevant 
 to our model. The reason behind this claim is that a TLA+ model allows stuttering by nature (which is also regarded as 
 an unique feature compared with most other models): the execution of a task could always be replaced with stuttering 
 steps. The only assumption required here is that the execution of a task should always be finished in finite time.

 2) The order of task execution in this model is quite obvious: all tasks in the same queue are always executed in the 
 same order as their submissions as long as the queue satisfies the first-in-first-out property, since any given queue 
 is only accessed by a single consumer and the executions of a consumer is by definition sequential.
*)

EXTENDS 
    Integers, 
    Sequences,
    TLC

CONSTANT
    ProducerCount, 
    ConsumerCount

ASSUME ProducerCount \in Nat
ASSUME ConsumerCount \in Nat

Producers == 1 .. ProducerCount
Consumers == 1 .. ConsumerCount

CONSTANT Nil

CONSTANT Task

(* common labels for any process *)
CONSTANT 
    L_Any,
    L_Reset

(* labels for producer submitting tasks *)
CONSTANT 
    L_Check_Concurrent_Close,
    L_Add_Consumer,
    L_Enqueue_Task,
    L_Signal_Consumer,
    L_Detect_Concurrent_Close

CONSTANT 
    L_Shutdown

(* labels for consumer main loop *)
CONSTANT 
    L_Check_Closed_Status,
    L_Dequeue_Task,
    L_Execute_Task,
    L_Clear_Active_Status,
    L_Check_Empty_Queue,
    L_Set_Active_Status_and_Continue,
    L_Self_Block

CONSTANT 
    (*
     This operator determines whether a producer should be stopped. By contract, once a producer was determined stopped, 
     it should remain stopped onwards. A stopped producer is not allowed to come back alive later. Any implementation of 
     this operator should respect this contract.

     The implementation of this operator is meant to be provided by the derived module which will be directly checked 
     with a model checker.
    *)
    ShouldProducerStop(_)

VARIABLE
    (* a flag indicating if this thread pool has been closed *)
    closed,
    (* task queue for each consumer *)
    taskQueues,
    (* a set recording all created consumers *)
    consumers,
    (* a per-consumer status used for park/unpark *)
    activeStatuses,
    (* per-producer context *)
    producerContexts,
    (* per-consumer context *)
    consumerContexts

VARIABLE 
    (* count of operations have been executed for each producer *)
    operationCounts

(* process control for consumers *)
(* Note: These variables are meant to be invisible to this module. Do not manipulate them directly! *)
VARIABLE 
    consumerActivations,
    consumerPermits,
    consumerTerminations
ConsumerControl == INSTANCE ProcessControl WITH 
    Processes <- Consumers, 
    activeStatuses <- consumerActivations, 
    permits <- consumerPermits,
    terminationStatuses <- consumerTerminations

varConsumerControl == <<consumerActivations, consumerPermits, consumerTerminations>>

vars == <<
    varConsumerControl,
    operationCounts,
    closed,
    taskQueues,
    consumers,
    activeStatuses,
    producerContexts, 
    consumerContexts
>>

InitProducerContext == [
    pc |-> L_Any,
    consumerId |-> Nil,
    consumersToShutdown |-> {}
]

InitConsumerContext == [
    pc |-> L_Any,
    task |-> Nil
]
----
(* Task submission via a producer: *)

UpdateProducerContext(p, ContextGenerator(_)) == 
    producerContexts' = [producerContexts EXCEPT ![p] = ContextGenerator(@)]

AssertValidProducer(p) == Assert(p \in Producers, "Invalid producer ID.")

MakeTask(p) == Task

IncreaseOperationCounter(p) == 
    operationCounts' = [operationCounts EXCEPT ![p] = @ + 1]

_CheckConcurrentClose(p) == 
    /\ IncreaseOperationCounter(p)
    /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT 
        !.pc = IF closed = FALSE THEN L_Add_Consumer ELSE L_Any])

_AddConsumer(p, consumerId) ==
    LET _consumerCreated == consumerId \notin consumers IN 
    /\ \/ /\ _consumerCreated
          /\ consumers' = consumers \cup {consumerId}
       \/ /\ ~_consumerCreated
          /\ UNCHANGED consumers
    /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT 
        !.pc = L_Enqueue_Task, 
        !.consumerId = consumerId])

_EnqueueTask(p) ==
    (*
     Implementation hints:

     Since it is possible for a consumer to concurrently nulling out this reference to task queue when a "shutdown" 
     operation was detected, the manipulation to that queue in this sub action should be implemented atomically in 
     practice, i.e., it should be regarded as an "read-and-then-update" operation.

     Fortunately, it quite easy to implement that in a fast lock-free manner. The pseudo code is similar to the 
     following one:
     
     // Get a local reference to the task queue.
     var q = [Get the reference to the corresponding queue.];
     if (q != null) {
         // Do task enqueue via the local reference.
         enqueue(q);
         // Double check that the reference does not change.
         if (q != [Get the reference to the corresponding queue again.]) {
            [Cancel current task.]
         }
     }
    *)
    LET _q == taskQueues[producerContexts[p].consumerId] IN 
    (* There is a concurrent close, since the consumer has removed this queue. *)
    \/ /\ _q = Nil
       (* Cancel the task or execute it under the caller's context/thread here. *) 
       /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Reset])
       /\ UNCHANGED taskQueues
    (* This thread pool is still not closed, at least at this instant. *)
    \/ /\ _q /= Nil
       /\ taskQueues' = [taskQueues EXCEPT ![producerContexts[p].consumerId] = Append(@, MakeTask(p))]
       /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Signal_Consumer])

_SignalConsumer(p) ==
    LET _consumer == producerContexts[p].consumerId
        _consumerInactive == activeStatuses[_consumer] = FALSE IN 
    /\ \/ /\ _consumerInactive
          /\ activeStatuses' = [activeStatuses EXCEPT ![_consumer] = TRUE]
          /\ ConsumerControl!Unpark(_consumer)
       \/ /\ ~_consumerInactive
          /\ UNCHANGED <<activeStatuses, varConsumerControl>>
    /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Reset])

(* This sub action is currently not in use. *)
_DetectConcurrentClose(p) == 
    (* Carry out any clean up here. *)
    LET _consumer == producerContexts[p].consumerId IN 
    /\ \/ /\ closed = TRUE
          /\ taskQueues' = [taskQueues EXCEPT ![_consumer] = <<>>]
       \/ /\ closed = FALSE
          /\ UNCHANGED taskQueues
    /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Reset])

_ResetProducerContext(p) == UpdateProducerContext(p, LAMBDA x: InitProducerContext)

SubmitTask(p) ==
    AssertValidProducer(p) /\
    LET _pc == producerContexts[p].pc IN 
    \/ /\ _pc = L_Any \/ _pc = L_Check_Concurrent_Close
       /\ _CheckConcurrentClose(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            taskQueues,
            consumers,
            activeStatuses,
            consumerContexts
            >>
    \/ /\ _pc = L_Add_Consumer
       /\ _AddConsumer(p, CHOOSE x \in Consumers: TRUE)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            taskQueues,
            activeStatuses,
            consumerContexts,
            operationCounts
            >>
    \/ /\ _pc = L_Enqueue_Task
       /\ _EnqueueTask(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            consumers,
            activeStatuses,
            consumerContexts,
            operationCounts
            >>
    \/ /\ _pc = L_Signal_Consumer
       /\ _SignalConsumer(p)
       /\ UNCHANGED <<
            closed,
            taskQueues,
            consumers,
            consumerContexts,
            operationCounts
            >>
    \/ /\ _pc = L_Detect_Concurrent_Close
       /\ _DetectConcurrentClose(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            consumers,
            activeStatuses,
            consumerContexts,
            operationCounts
            >>
    \/ /\ _pc = L_Reset
       /\ _ResetProducerContext(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            taskQueues,
            consumers,
            activeStatuses,
            consumerContexts,
            operationCounts
            >>
----
(* Thread pool shutdown via a producer: *)
Shutdown(p) == 
    AssertValidProducer(p) /\
    LET _pc == producerContexts[p].pc 
        _candidates == producerContexts[p].consumersToShutdown
        _selection == IF _candidates = {} THEN Nil ELSE CHOOSE x \in _candidates: TRUE IN 
    (* This is a reentrant close or a "close after a close". *)
    \/ /\ _pc = L_Any /\ closed = TRUE
       /\ IncreaseOperationCounter(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            taskQueues,
            consumers,
            activeStatuses,
            producerContexts,
            consumerContexts
            >>
    (* This is the initial close. *)
    \/ /\ _pc = L_Any /\ closed = FALSE
       /\ IncreaseOperationCounter(p)
       /\ closed' =TRUE
       /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT 
            !.pc = L_Shutdown,
            !.consumersToShutdown = consumers])
       /\ UNCHANGED <<
            varConsumerControl,
            taskQueues,
            consumers,
            activeStatuses,
            consumerContexts
            >>
    (* Sub actions: wake up known consumers one-by-one. *)
    \/ /\ _pc = L_Shutdown
       /\ \/ /\ _candidates = {}
             /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Reset])
             /\ UNCHANGED <<varConsumerControl>>
          \/ /\ _candidates /= {}
             /\ ConsumerControl!Unpark(_selection)
             /\ UpdateProducerContext(p, LAMBDA x: [x EXCEPT 
                !.pc = L_Shutdown,
                !.consumersToShutdown = _candidates \ {_selection}])
       /\ UNCHANGED <<
            closed,
            taskQueues,
            consumers,
            activeStatuses,
            consumerContexts,
            operationCounts
            >>
----  
(* Main loop for consumer: *)

UpdateConsumerContext(p, ContextGenerator(_)) == 
    consumerContexts' = [consumerContexts EXCEPT ![p] = ContextGenerator(@)]

AssertValidConsumer(p) == Assert(p \in Consumers, "Invalid consumer ID.")

_CheckClosedStatus(p) == 
    \/ /\ closed
       (* Clear all pending tasks here. *)
       /\ taskQueues' = [taskQueues EXCEPT ![p] = Nil]
       /\ activeStatuses' = [activeStatuses EXCEPT ![p] = FALSE]
       /\ ConsumerControl!Terminate(p)
       /\ UNCHANGED consumerContexts
    \/ /\ ~closed
       /\ UpdateConsumerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Dequeue_Task])
       /\ UNCHANGED <<activeStatuses, taskQueues, varConsumerControl>>

_DequeueTask(p) == 
    LET _q == taskQueues[p]
        _queueLength == Len(_q)
        _queueEmpty == _queueLength = 0
        _current_task == IF _queueEmpty THEN Nil ELSE Head(_q) IN 
    /\ \/ /\ ~_queueEmpty
          /\ taskQueues' = [taskQueues EXCEPT ![p] = IF _queueLength = 1 THEN <<>> ELSE SubSeq(@, 1, _queueLength - 1)]
       \/ /\ _queueEmpty
          /\ UNCHANGED taskQueues
    /\ UpdateConsumerContext(p, LAMBDA x: [x EXCEPT 
        !.pc = IF _current_task /= Nil THEN L_Execute_Task ELSE L_Clear_Active_Status,
        !.task = _current_task])

_ExecuteTask(p) == 
    /\ TRUE \* executing the task
    /\ UpdateConsumerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Check_Closed_Status])

_ClearActiveStatus(p) == 
    /\ activeStatuses' = [activeStatuses EXCEPT ![p] = FALSE]
    /\ UpdateConsumerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Check_Empty_Queue])

_SetActiveStatusAndContinue(p) == 
    /\ activeStatuses' = [activeStatuses EXCEPT ![p] = TRUE]
    /\ UpdateConsumerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Check_Closed_Status])
    
_SelfBlock(p) == 
    /\ ConsumerControl!Park(p)
    /\ UpdateConsumerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Set_Active_Status_and_Continue])

_CheckEmptyQueue(p) == 
    LET _queueEmpty == Len(taskQueues[p]) = 0 IN 
    \/ /\ ~_queueEmpty
       /\ UpdateConsumerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Set_Active_Status_and_Continue])
    \/ /\ _queueEmpty
       /\ UpdateConsumerContext(p, LAMBDA x: [x EXCEPT !.pc = L_Self_Block])

(*
 State transition diagram:
       ----------------------------------------------------------
       v                                |                       |
 CheckCloseStatus -> DequeueTask -> ExecuteTask          SetActiveStatusAndContinue <---
                            |                                  /\                      |
                            ------> ClearActiveStatus -> CheckEmptyQueue -> SelfBlock --
*)
RunConsumer(p) ==
    AssertValidConsumer(p) /\
    LET _pc == consumerContexts[p].pc
        _currentTask == consumerContexts[p].task IN 
    \/ /\ _pc = L_Any \/ _pc = L_Check_Closed_Status
       /\ _CheckClosedStatus(p)
       /\ UNCHANGED <<
            closed,
            consumers,
            producerContexts, 
            operationCounts
            >>
    \/ /\ _pc = L_Dequeue_Task
       /\ _DequeueTask(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            consumers,
            activeStatuses,
            producerContexts, 
            operationCounts
            >>
    \/ /\ _pc = L_Execute_Task
       /\ _ExecuteTask(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            taskQueues,
            consumers,
            activeStatuses,
            producerContexts, 
            operationCounts
            >>
    \/ /\ _pc = L_Clear_Active_Status
       /\ _ClearActiveStatus(p)
       /\ UNCHANGED <<
             varConsumerControl,
             closed,
             taskQueues,
             consumers,
             producerContexts, 
             operationCounts
             >>
    \/ /\ _pc = L_Check_Empty_Queue
       /\ _CheckEmptyQueue(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            taskQueues,
            consumers,
            activeStatuses,
            producerContexts, 
            operationCounts
            >>
    \/ /\ _pc = L_Set_Active_Status_and_Continue
       /\ _SetActiveStatusAndContinue(p)
       /\ UNCHANGED <<
            varConsumerControl,
            closed,
            taskQueues,
            consumers,
            producerContexts, 
            operationCounts
            >>
    \/ /\ _pc = L_Self_Block
       /\ _SelfBlock(p)
       /\ UNCHANGED <<
            closed,
            taskQueues,
            consumers,
            activeStatuses,
            producerContexts, 
            operationCounts
            >>
----
(* This section focuses on model simulation: *)

(*
 This is the set of all currently running consumer (worker) processes with each one of them satisfies all of the 
 following conditions:
 1. It is a valid consumer (has a valid ID).
 2. It has already been created by the producer/caller (due the lazy initialization implementation).
 3. It has been decided by the "ProcessControl" module that this process is in a running state.
*)
ActiveConsumers == Consumers \cap consumers \cap ConsumerControl!ActiveProcesses

(*
 This is the set of all non-stopped producers (caller) processes. A stopped producer should satisfy all of the following
 conditions:
 1. It is a valid producer (has a valid ID).
 2. Operator ShouldProducerStop(_) returns TRUE for this producer.
 3. It is in an appropriate process context which means its top level operation is completed, i.e. ".pc = L_Any". This 
    condition basically says that a producer should not stop in the middle of a running operation, which guarantees the 
    integrity of a operation.

 In practice, condition 3 is quite hard to be met, since a caller thread could crash in the middle of any executing 
 function. This should be regarded as a general issue which is beyond the scope of this model.
*)
ActiveProducers == {p \in Producers: ~(ShouldProducerStop(p) /\ producerContexts[p].pc = L_Any)}

Init == 
    /\ ConsumerControl!Init
    /\ closed = FALSE
    /\ taskQueues = [p \in Consumers |-> <<>>]
    /\ consumers = {}
    /\ activeStatuses = [p \in Consumers |-> FALSE]
    /\ producerContexts = [p \in Producers |-> InitProducerContext]
    /\ consumerContexts = [p \in Consumers |-> InitConsumerContext]
    /\ operationCounts = [p \in Producers |-> 0]

RunAProducer == \E p \in ActiveProducers: 
    \/ SubmitTask(p)
    \/ Shutdown(p)

RunAConsumer == \E p \in ActiveConsumers: RunConsumer(p)

Next ==
    \/ RunAProducer
    \/ RunAConsumer
    (* final state: *)
    \/ /\ ActiveConsumers \cup ActiveProducers = {} 
       /\ UNCHANGED vars

(* Fairness of producer/consumer scheduling: *)
Liveness == 
    /\ WF_vars(RunAProducer)
    /\ WF_vars(RunAConsumer)

Spec == Init /\ [][Next]_vars /\ Liveness
----
(* This section focuses on type invariance only. *)

CommonLabels == {L_Any, L_Reset}

ProducerLabels == {
    L_Check_Concurrent_Close,
    L_Add_Consumer,
    L_Enqueue_Task,
    L_Signal_Consumer,
    L_Detect_Concurrent_Close,

    L_Shutdown
}

ConsumerLabels == {
    L_Check_Closed_Status,
    L_Dequeue_Task,
    L_Execute_Task,
    L_Clear_Active_Status,
    L_Check_Empty_Queue,
    L_Set_Active_Status_and_Continue,
    L_Self_Block
}

ProducerContextEnum == [
    pc: ProducerLabels \cup CommonLabels,
    consumerId: Consumers \cup {Nil},
    consumersToShutdown: SUBSET Consumers
]

ConsumerContextEnum == [
    pc: ConsumerLabels \cup CommonLabels,
    task: {Nil, Task}
]

ProducerContextTypeInv == \A p \in Producers: producerContexts[p] \in ProducerContextEnum
ConsumerContextTypeInv == \A p \in Consumers: consumerContexts[p] \in ConsumerContextEnum
ContextTypeInv == ProducerContextTypeInv /\ ConsumerContextTypeInv

ClosedStatusTypeInv == closed \in BOOLEAN 

TaskQueueTypeInv == \A p \in Consumers:
    LET _q == taskQueues[p] IN 
    _q = Nil \/ Len(_q) >= 0

ConsumerIdSetTypeInv == consumers \subseteq Consumers

ActiveStatusTypeInv == \A p \in Consumers: activeStatuses[p] \in BOOLEAN 

OperationCountTypeInv == \A p \in Producers: operationCounts[p] \in (Nat \cup {0})

ShouldProducerStopTypeInv == \A p \in Producers: ShouldProducerStop(p) \in BOOLEAN 

TypeInv == 
    /\ ContextTypeInv
    /\ ClosedStatusTypeInv
    /\ TaskQueueTypeInv
    /\ ConsumerIdSetTypeInv
    /\ ActiveStatusTypeInv
    /\ OperationCountTypeInv
    /\ ShouldProducerStopTypeInv

THEOREM Spec => []TypeInv
----
(* This section focuses on implementation related safety properties (unit tests?): *)

(* Any consumer before creation should not have a modified context or active status. *)
NonCreatedConsumerHasNoContext == 
    LET _xConsumers == {p \in Consumers: p \notin consumers} IN 
    \A p \in _xConsumers: 
        /\ consumerContexts[p] = InitConsumerContext
        /\ activeStatuses[p] = FALSE

THEOREM Spec => []NonCreatedConsumerHasNoContext
----
(* This section focuses on basic safety properties: *)

(* 
 Any non-terminated consumer with the active status set is guaranteed to be in a running/active state. But the opposite 
 is not true. Refer to the next formula for verification.
*)
ActiveStatusImpliesRunning == \A p \in {x \in Consumers: x \notin ConsumerControl!TerminatedProcesses}:
    activeStatuses[p] = TRUE => p \in ConsumerControl!ActiveProcesses

(* A cleared active status does *NOT* sufficiently imply that the corresponding non-terminated consumer is inactive. *)
ActiveStatusDoesNotImplyBlocking == ~(\A p \in {x \in Consumers: x \notin ConsumerControl!TerminatedProcesses}: 
    activeStatuses[p] = FALSE => p \notin ConsumerControl!ActiveProcesses)

THEOREM Spec => 
    /\ []ActiveStatusImpliesRunning
    /\ []ActiveStatusDoesNotImplyBlocking
----
(* This section focuses on liveness properties: *)
(* Note: Verification of these properties via TLC is extremely time-consuming. *)

(*
 Once operator ShouldProducerStop(_) returned TRUE, it should eventually always return TRUE.
 
 Actually, the contract of ShouldProducerStop(_) should be more strict than above, but currently I have no idea about 
 how to express that using existing temporal formulas. Refer to the comments of ShouldProducerStop(_) for more details.
*)
ProducerTerminationPattern == \A p \in Producers:
    ShouldProducerStop(p) ~> <>[]ShouldProducerStop(p)

(* Eventually, all producers and consumers always become inactive. *)
EventuallyAlwaysInactive == <>[](ActiveProducers \cup ActiveConsumers = {})

(* Eventually, all task queues should always be empty or null. *)
EventuallyAlwaysTaskQueueEmpty == \A p \in Consumers:
    <>[](taskQueues[p] \in {Nil, <<>>})

(* The termination of all producers leads to the inactivation of all consumers. *)
ProducerTerminationLeadsToConsumerInactivation == 
    (\A p \in Producers: ShouldProducerStop(p)) ~> ActiveConsumers = {}

(*
 For a thread pool that never shutdown:
 The existence of any producer ready to submit a task leads to at least one non-empty task queue.
*)
ActiveProducerLeadsToNonEmptyTaskQueue == 
    /\ [](closed = FALSE)
    /\ \E p \in ActiveProducers: producerContexts[p].pc = L_Any
    ~> \E p \in Consumers: Len(taskQueues[p]) > 0

(*
 For a thread pool that never shutdown:
 Any non-empty task queue leads to at least one running consumer.
*)
NonEmptyTaskQueueLeadsToRunningConsumer == 
    /\ [](closed = FALSE)
    /\ \A p \in Consumers: Len(taskQueues[p]) > 0
    ~> ActiveConsumers /= {}

(*
 More specifically, for a thread pool that never shutdown:
 Any non-empty task queue leads to the corresponding running consumer.
*)
NonEmptyTaskQueueLeadsToCorrespondindRunningConsumer == \A p \in Consumers:
    /\ [](closed = FALSE)
    /\ Len(taskQueues[p]) > 0 
    ~> p \in ActiveConsumers

(*
 After a "shutdown" operation was carried out, all created consumers will be terminated.
 In practice, this property guarantees that there is no thread leak after the thread pool shutdown.

 Further more, the specification of ProcessControl module has verified the following liveness property:
 Once a process is in a terminated state, it will eventually always in that state. Refer to the underlying module for 
 more details.
*)
ShutdownLeadsToConsumerTermination == closed = TRUE ~> \A p \in Consumers:
    p \in consumers => p \in ConsumerControl!TerminatedProcesses

THEOREM Spec => 
    /\ ProducerTerminationPattern
    /\ EventuallyAlwaysInactive
    /\ EventuallyAlwaysTaskQueueEmpty
    /\ ProducerTerminationLeadsToConsumerInactivation
    /\ ActiveProducerLeadsToNonEmptyTaskQueue
    /\ NonEmptyTaskQueueLeadsToRunningConsumer
    /\ NonEmptyTaskQueueLeadsToCorrespondindRunningConsumer
    /\ ShutdownLeadsToConsumerTermination
====
