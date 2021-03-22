------------------------------- MODULE skeen -------------------------------

EXTENDS Integers,  FiniteSets, Sequences, TLC

a <: b == a


VARIABLE clock, phase, localTS, globalTS, rcvdMcastID, mcastedID,   
            inTransit, delivered, proposeTS
  
vars == << clock, phase, localTS, globalTS, rcvdMcastID, mcastedID, 
            inTransit, delivered, proposeTS >>

CONSTANT N, M,  GroupDest, Mcaster, MaxClock

Proc == 1..N
McastID == 1..M
MType == 10
PType == 11
Start == 12
Proposed == 13 
Committed == 14

ASSUME
  /\ N \in Int
  /\ \A id \in McastID : GroupDest[id] \in SUBSET Int 
  /\ MType \in Int
  /\ PType \in Int
  /\ Start \in Int
  /\ Proposed \in Int
  /\ Committed \in Int
  /\ M = Cardinality(McastID)

McastMsgPhase == {Start, Proposed, Committed}
                       
McastPhase == [McastID -> McastMsgPhase]                              

\* TimestampNull: used in the initialization
GroupNull == 0 
TimeNull == 0
TimestampNull == [t |-> TimeNull, g |-> GroupNull] <: [t |-> Int, g |-> Int]

Time == 1..MaxClock    
ProcWithNull == 0..N            
            
TimestampSet == [t : Time, g : Proc] \cup {TimestampNull} \* <: {[t |-> Int, g |-> Int]} ) \cup ({TimestampNull}  <: {[g : Int, t : Int]})     
McastMsgSet   == [t : Time, id : McastID, type : {MType}, source : Proc] <: {[type |-> Int, t |-> Int, id |-> Int, source |-> Int]}  
ProposeMsgSet == [t : Time, id : McastID, type : {PType}, source : Proc] <: {[type |-> Int, t |-> Int, id |-> Int, source |-> Int]}
InTransitMsgSet == McastMsgSet \cup ProposeMsgSet

         
  






(* The relation "less than" is asymmetric. In other words, for every pair of Broadcast messages m1 and m2, if there exists 
   server s1 such that s1 delivers m1 before m2, there exists no server s2 such that (i) s2 delivers m2 before delivering m1,  
   or (ii) s2 delivered m2, but not delivered m1.
 *) 

      

                 
Stamp(t, g) == [time |-> t, group |-> g]


                                           
\* The primitive for receiving one message
\*  - There exisits implicitly an assumption about the hiararchy of messages in transit.
\*    This assumption is described by the first guards.
\*  - A message sent by a process to itself should be received immediately. In other words, 
\*    a process should receive all messages which it send to itself before
\*    receiving messages from others. 
\*  - m is the message which proc rcver has received in this transition.
\*  - slot is the slot containing m.
\*  - Increase head[snder][rcver] by 1 to mark that proc rcver has received message m.
\*  - Messages from head'[snder][rcver] to rear[snder][rcver] are in transit.  
\*  - Push message m to a list of message which proc rcver has received. 

                                            
                          
\* The initialized states
\*  - Only one leader in the initialize state, other Proces are followers.
\*  - No faults has happened.
\*  - No client requests are stored at every Procs.   
\*  - Both ballot and cballot are initialized with 0
\*  - No client requests are known by a majority of Procs.
\*  - Every client has not received any message.
\*  - No message is in transit, in every communication channel.
Init ==  
  /\ clock = [p \in Proc |-> 0]
  /\ phase = [p \in Proc |-> [m \in McastID |-> Start]]
  /\ localTS = [p \in Proc |-> [m \in McastID |-> TimestampNull]]
  /\ globalTS = [p \in Proc |-> [m \in McastID |-> TimestampNull]]
  /\ delivered = [p \in Proc |-> [m \in McastID |-> FALSE]]
  /\ rcvdMcastID = [p \in Proc |-> ({} <: {Int} ) ] 
  /\ proposeTS = [p \in Proc |-> [id \in McastID |-> ({} <: {[type |-> Int, t |-> Int, id |-> Int, source |-> Int]}) ] ]  
  /\ mcastedID = ({} <: {Int})
  /\ inTransit = [p \in Proc |-> [q \in Proc |-> ({} <: {[type |-> Int, t |-> Int, id |-> Int, source |-> Int]})]]
  
  
  
                                      

Max(a, b) == IF a > b THEN a ELSE b
       
Multicast(mid) ==    
  LET snder == Mcaster[mid]
  IN  /\ mid \notin mcastedID   
      /\ clock[snder] < MaxClock 
      /\ snder \in GroupDest[mid] 
      /\ mcastedID' = mcastedID \cup {mid}
      /\ LET time == clock[snder] + 1
             msg ==  ([ type |-> MType, id |-> mid, t |-> time, source |-> snder ] <: [type |-> Int, t |-> Int, source |-> Int, id |-> Int])
         IN   /\ inTransit' = [p \in Proc |-> [q \in Proc |-> 
                                  IF p = snder /\ q \in GroupDest[mid]
                                  THEN inTransit[p][q] \cup {msg}
                                  ELSE inTransit[p][q]]]
              /\ clock' = [ clock EXCEPT ![snder] = time ]
              /\ UNCHANGED << phase, proposeTS, rcvdMcastID, localTS, globalTS, delivered >>
              
      
   
isYoungestMsg(snder, rcver, msg) ==
  \A m \in inTransit[snder][rcver] : msg.t <= m.t   
   
ReceiveMulticast(snder, rcver, msg) ==   
  /\ clock[rcver] < MaxClock
  /\ msg.type = MType      
  /\ isYoungestMsg(snder, rcver, msg)
  /\ rcvdMcastID' = [rcvdMcastID EXCEPT ![rcver] = rcvdMcastID[rcver] \cup {msg.id}] 
  /\ UNCHANGED << proposeTS, globalTS, delivered, mcastedID >>
  /\ LET mid == msg.id
         time == clock[rcver] + 1
         newTS == [ t |-> time, g |-> rcver ]                             
         newMsg == ([ type |-> PType, id |-> mid, source |-> rcver, t |-> time ] <: [type |-> Int, t |-> Int, source |-> Int, id |-> Int])                       
     IN /\ clock' = [clock EXCEPT ![rcver] = clock[rcver] + 1]        
        /\ localTS' = [localTS EXCEPT ![rcver][mid] = newTS]          
        /\ phase' = [phase EXCEPT ![rcver][mid] = Proposed]
        /\ IF snder # rcver
           THEN inTransit' = [p \in Proc |-> [q \in Proc |-> 
                                  IF p = rcver /\ q \in GroupDest[mid]
                                  THEN inTransit[p][q] \cup {newMsg}                                      
                                  ELSE IF p = snder /\ q = rcver
                                       THEN inTransit[p][q] \ {msg}
                                       ELSE inTransit[p][q] ]] 
            ELSE inTransit' = [p \in Proc |-> [q \in Proc |-> 
                                  IF p = rcver /\ q = rcver
                                  THEN (inTransit[p][q] \cup {newMsg}) \ {msg}
                                  ELSE IF p = rcver /\ q \in GroupDest[mid]
                                       THEN inTransit[p][q] \cup {newMsg}                                      
                                       ELSE inTransit[p][q] ]]
        
   
   
Less(ts1, ts2) ==
  \/ ts1.t < ts2.t
  \/ /\ ts1.t = ts2.t
     /\ ts1.g < ts2.g   



                                
CanDeliver(p, id) ==
  /\ ~delivered[p][id] 
  /\ phase'[p][id] = Committed
  /\ \A mid \in rcvdMcastID'[p] : 
        phase'[p][mid] = Proposed => Less(globalTS'[p][id], localTS'[p][mid]) 
                                                                       
 
HasAllProposes(rcver, id) ==
  \A p \in GroupDest[id] : \E m \in proposeTS'[rcver][id] : m.source = p
 
(* 
PickOwnerOfMaxTS(rcver, id) == 
  CHOOSE p \in Proc : 
    /\ proposeTS'[rcver][p][id] # TimestampNull
    /\ \A q \in Proc : proposeTS'[rcver][q][id] # TimestampNull 
                          => ~Less(proposeTS'[rcver][p][id], proposeTS'[rcver][q][id]) 
 *)
PickMsgWithMaxTS(rcver, id) == 
  CHOOSE m \in proposeTS'[rcver][id] : 
    \A m1 \in proposeTS'[rcver][id] : 
        \/ m1.t < m.t
        \/ /\ m1.t = m.t 
           /\ m1.source <= m.source

 
ReceivePropose(snder, rcver, msg) ==   
  /\ msg.type = PType
  /\ isYoungestMsg(snder, rcver, msg)
  /\ inTransit' = [inTransit EXCEPT ![snder][rcver] = inTransit[snder][rcver] \ {msg}]  
  /\ LET ts == [ t |-> msg.t, g |-> msg.source]
         id == msg.id
     IN /\ UNCHANGED << localTS, mcastedID, rcvdMcastID  >>
        /\ proposeTS' = [proposeTS EXCEPT ![rcver][id] = proposeTS[rcver][id] \cup {msg} ]
        (*
        /\ IF HasAllProposes(rcver, id)        
           THEN LET p == PickOwnerOfMaxTS(rcver, id)
                    maxTS == proposeTS'[rcver][p][id]               
                IN /\ globalTS' = [globalTS EXCEPT ![rcver][id] = maxTS]                
                   /\ clock' = [clock EXCEPT ![rcver]  = Max(clock[rcver], maxTS.t)]                
                   /\ phase' = [phase EXCEPT ![rcver][id] = Committed]                
                   /\ delivered' = [ delivered EXCEPT ![rcver] = [mid \in McastID |-> 
                                        IF ~delivered[rcver][mid]
                                        THEN CanDeliver(rcver, mid)
                                        ELSE delivered[rcver][mid] ]]                           
           ELSE UNCHANGED <<phase, globalTS, clock, delivered>>
          *)      
        /\ IF HasAllProposes(rcver, id)        
           THEN LET m == PickMsgWithMaxTS(rcver, id)       
                    maxTS == [ g |-> m.source, t |-> m.t ]                             
                IN /\ globalTS' = [globalTS EXCEPT ![rcver][id] = maxTS]                
                   /\ clock' = [clock EXCEPT ![rcver]  = Max(clock[rcver], maxTS.t)]                
                   /\ phase' = [phase EXCEPT ![rcver][id] = Committed]                
                   /\ delivered' = [ delivered EXCEPT ![rcver] = [mid \in McastID |-> 
                                        IF ~delivered[rcver][mid]
                                        THEN CanDeliver(rcver, mid)
                                        ELSE delivered[rcver][mid] ]]                           
           ELSE UNCHANGED <<phase, globalTS, clock, delivered>>
 
     
Next == 
  \/ \E m \in McastID : Multicast(m) 
  \/ \E snder, rcver \in Proc : \E msg \in inTransit[snder][rcver] : ReceiveMulticast(snder, rcver, msg)  
  \/ \E snder, rcver \in Proc : \E msg \in inTransit[snder][rcver] : ReceivePropose(snder, rcver, msg)
  \/ UNCHANGED vars


Spec == 
  /\ Init 
  /\ [][Next]_vars
  /\ WF_vars( \/ \E m \in McastID : Multicast(m) 
              \/ \E snder, rcver \in Proc : \E msg \in inTransit[snder][rcver] : ReceiveMulticast(snder, rcver, msg)  
              \/ \E snder, rcver \in Proc : \E msg \in inTransit[snder][rcver] : ReceivePropose(snder, rcver, msg) )    


    
Validity == \A p \in Proc : \A id \in McastID : delivered[p][id] => id \in mcastedID

McastOrdering == { ordering \in [McastID -> 1..M] : (\A id1, id2 \in McastID : ordering[id1] = ordering[id2] => id1 = id2)}

 
ValidOwnedLocalTS ==
  /\ ( \A id \in McastID : \A p \in Proc \ GroupDest[id] : localTS[p][id] = TimestampNull )
  /\ ( \A id \in McastID : \A p \in GroupDest[id] :
          (localTS[p][id] # TimestampNull 
                => ( /\ id \in mcastedID
                     /\ localTS[p][id].g = p ))) 
      
      
 
ValidInTransitProposeTS ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc : \A m \in inTransit[snder][rcver] : m.id # id )
  /\ ( \A id \in McastID : \A snder \in Proc \ GroupDest[id] : \A rcver \in Proc : \A m \in inTransit[snder][rcver] : m.id # id )
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A snder \in Proc : \A m \in inTransit[snder][rcver] : 
            m.id = id => id \in mcastedID)            
  
ValidRcvdProposeTS ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc : 
          proposeTS[rcver][id] = ({} <: {[type |-> Int, t |-> Int, id |-> Int, source |-> Int]} ))          
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A msg \in proposeTS[rcver][id] :
          /\ msg.id \in mcastedID )
  
                  
BoundedClock == \A p \in Proc : clock[p] <= MaxClock

ValidGlobalTS ==
  /\ \A id \in McastID : \A rcver \in GroupDest[id] :  
          globalTS[rcver][id] # TimestampNull => id \in mcastedID                        
  /\ \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : 
          globalTS[rcver][id] = TimestampNull
                  
                                                               
             
ValidInTransitMcast ==
  /\ \A snder, rcver \in Proc : \A id \in McastID : \A m \in inTransit[snder][rcver] :
        (m.type = MType /\ m.id = id) => (snder = Mcaster[id] /\ id \in mcastedID)
    
  

TypeOK ==
  /\ clock \in [Proc -> Time \cup {TimeNull}]
  /\ localTS \in [Proc -> [McastID -> TimestampSet]]   
  /\ globalTS \in [Proc -> [McastID -> TimestampSet]]   
  /\ phase \in [Proc -> [McastID -> {Start, Proposed, Committed}]]  
  /\ rcvdMcastID \in [Proc -> SUBSET McastID]
  /\ mcastedID \in SUBSET McastID   
  /\ inTransit \in [Proc -> [Proc -> SUBSET InTransitMsgSet]]  
  /\ delivered \in [Proc -> [McastID -> BOOLEAN]] 
  /\ proposeTS \in [Proc -> [McastID -> SUBSET ProposeMsgSet]]
  
ValidPhase ==
  \A p \in Proc : \A id \in McastID :
    ( /\ phase[p][id] = Committed => (\A q \in GroupDest[id] : \E m \in proposeTS[p][id] : m.source = q )
      /\ phase[p][id] = Committed => globalTS[p][id] # TimestampNull)
                  
  
IndInv ==
  /\ TypeOK   
  /\ Validity
  /\ ValidOwnedLocalTS 
  /\ ValidInTransitProposeTS  
  /\ ValidRcvdProposeTS
  /\ BoundedClock  
  /\ ValidGlobalTS                     
  /\ ValidInTransitMcast  
  /\ ValidPhase
  
  
  
(* Initial state *)
State0 ==
  clock = 1 :> 0
    /\ delivered = 1 :> (1 :> FALSE @@ 2 :> FALSE)
    /\ globalTS = 1 :> (1 :> [g |-> 1, t |-> 4] @@ 2 :> [g |-> 0, t |-> 0])
    /\ inTransit = 1 :> (1 :> {[id |-> 1, source |-> 1, t |-> 5, type |-> 10]})
    /\ localTS = 1 :> (1 :> [g |-> 0, t |-> 0] @@ 2 :> [g |-> 0, t |-> 0])
    /\ mcastedID = {1}
    /\ phase = 1 :> (1 :> 14 @@ 2 :> 12)
    /\ proposeTS
      = 1 :> (1 :> {[id |-> 1, source |-> 1, t |-> 1, type |-> 11]} @@ 2 :> {})
    /\ rcvdMcastID = 1 :> { 1, 2 }

(* Transition 2 to State1 *)
State1 ==
  clock = 1 :> 1
    /\ delivered = 1 :> (1 :> FALSE @@ 2 :> FALSE)
    /\ globalTS = 1 :> (1 :> [g |-> 1, t |-> 4] @@ 2 :> [g |-> 0, t |-> 0])
    /\ inTransit = 1 :> (1 :> {[id |-> 1, source |-> 1, t |-> 1, type |-> 11]})
    /\ localTS = 1 :> (1 :> [g |-> 1, t |-> 1] @@ 2 :> [g |-> 0, t |-> 0])
    /\ mcastedID = {1}
    /\ phase = 1 :> (1 :> 13 @@ 2 :> 12)
    /\ proposeTS
      = 1 :> (1 :> {[id |-> 1, source |-> 1, t |-> 1, type |-> 11]} @@ 2 :> {})
    /\ rcvdMcastID = 1 :> { 1, 2 }

    


=============================================================================
\* Modification History
\* Last modified Wed Mar 17 10:01:03 CET 2021 by tran
\* Created Tue Mar 16 08:59:43 CET 2021 by tran
