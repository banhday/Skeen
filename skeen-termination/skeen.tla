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
      \* /\ snder = Mcaster[mid]
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

Done == 
  /\ \A id \in McastID : \A p \in GroupDest[id] : delivered[p][id]
  /\ UNCHANGED vars 
     
Next == 
  \/ \E m \in McastID : Multicast(m) 
  \/ \E snder, rcver \in Proc : \E msg \in inTransit[snder][rcver] : ReceiveMulticast(snder, rcver, msg)  
  \/ \E snder, rcver \in Proc : \E msg \in inTransit[snder][rcver] : ReceivePropose(snder, rcver, msg)
  \/ Done


Spec == 
  /\ Init 
  /\ [][Next]_vars
  /\ WF_vars( \/ \E m \in McastID : Multicast(m) 
              \/ \E snder, rcver \in Proc : \E msg \in inTransit[snder][rcver] : ReceiveMulticast(snder, rcver, msg)  
              \/ \E snder, rcver \in Proc : \E msg \in inTransit[snder][rcver] : ReceivePropose(snder, rcver, msg) )    


    
Validity == \A p \in Proc : \A id \in McastID : delivered[p][id] => id \in mcastedID

McastOrdering == { ordering \in [McastID -> 1..M] : (\A id1, id2 \in McastID : ordering[id1] = ordering[id2] => id1 = id2)}

(*
GlobalTotalOrdering ==
  \E ordering \in [McastID -> 1..M] :
    /\ \A id1, id2 \in McastID : ordering[id1] = ordering[id2] => id1 = id2
    /\ \A p \in Proc : \A id1, id2 \in McastID : 
            ( /\ globalTS[p][id1] # TimestampNull
              /\ globalTS[p][id2] # TimestampNull
              /\ ordering[id1] < ordering[id2] )
                    => Less(globalTS[p][id1], globalTS[p][id2])
 *)

GlobalTotalOrdering ==
  \E ordering \in McastOrdering : 
    /\ \A p \in Proc : \A id1, id2 \in McastID : 
            ( /\ globalTS[p][id1] # TimestampNull
              /\ globalTS[p][id2] # TimestampNull
              /\ ordering[id1] < ordering[id2] )
                    => Less(globalTS[p][id1], globalTS[p][id2])

 

AsymmetricOrdering == 
  \A id1, id2 \in McastID : \A p, q \in Proc :
      ( /\ globalTS[p][id1] # TimestampNull 
        /\ globalTS[p][id2] # TimestampNull 
        /\ globalTS[q][id1] # TimestampNull 
        /\ globalTS[q][id2] # TimestampNull
        /\ id1 # id2 )
            => ~(Less(globalTS[p][id1], globalTS[p][id2]) /\ Less(globalTS[q][id2], globalTS[q][id1]))
 
ConsistentGlobalTS1 ==  
  /\ \A id \in McastID : \A p, q \in Proc :
      ( /\ globalTS[p][id] # TimestampNull         
        /\ globalTS[q][id] # TimestampNull )
            => globalTS[p][id] = globalTS[q][id]
            
ConsistentGlobalTS2 ==            
  /\ \A id1, id2 \in McastID : \A p \in Proc :
      ( /\ id1 # id2
        /\ globalTS[p][id1] # TimestampNull         
        /\ globalTS[p][id2] # TimestampNull )
            => globalTS[p][id1] # globalTS[p][id2]    
 
ConsistentGlobalTS ==  
  /\ \A id \in McastID : \A p, q \in Proc :
      ( /\ globalTS[p][id] # TimestampNull         
        /\ globalTS[q][id] # TimestampNull )
            => globalTS[p][id] = globalTS[q][id]
  /\ \A id1, id2 \in McastID : \A p \in Proc :
      ( /\ id1 # id2
        /\ globalTS[p][id1] # TimestampNull         
        /\ globalTS[p][id2] # TimestampNull )
            => globalTS[p][id1] # globalTS[p][id2]    
  /\ \A id \in McastID : \A p \in Proc : globalTS[p][id] # TimestampNull <=> phase[p][id] = Committed
                    
                      
            
(*            
ValidOwnedLocalTS ==
  \A p \in Proc : \A id \in McastID :
      IF p \notin GroupDest[id]
      THEN localTS[p][id] = TimestampNull
      ELSE /\ localTS[p][id] = TimestampNull <=> id \notin rcvdMcastID[p]
           /\ localTS[p][id].t <= clock[p]
           /\ localTS[p][id] # TimestampNull => id \in mcastedID
 *)
ValidOwnedLocalTS ==
  /\ ( \A id \in McastID : \A p \in Proc \ GroupDest[id] : localTS[p][id] = TimestampNull )
  /\ ( \A id \in McastID : \A p \in GroupDest[id] :
          /\ localTS[p][id] = TimestampNull <=> id \notin rcvdMcastID[p]
          /\ localTS[p][id].t <= clock[p]
          /\ (localTS[p][id].g # GroupNull => localTS[p][id].t # TimeNull)
          /\ (localTS[p][id] # TimestampNull 
                => ( /\ id \in mcastedID
                     /\ localTS[p][id].g = p ))) 
  /\ \A id1, id2 \in McastID : \A p \in Proc :
        ((  /\ p \in GroupDest[id1] 
            /\ p \in GroupDest[id2]
            /\ id1 # id2
            /\ localTS[p][id1] # TimestampNull
            /\ localTS[p][id2] # TimestampNull )
                  => localTS[p][id1].t # localTS[p][id2].t )                     
      
(*      
ValidInTransitProposeTS ==
  \A rcver \in Proc : \A id \in McastID :
      IF rcver \notin GroupDest[id]
      THEN \A snder \in Proc : \A m \in inTransit[snder][rcver] : m.id # id
      ELSE \A snder \in Proc : \A m \in inTransit[snder][rcver] : 
                  (m.id = id /\ m.type = PType) 
              =>  ( /\ m.t = localTS[snder][id].t 
                    /\ id \in rcvdMcastID[snder] 
                    /\ id \in mcastedID )                    
 *)
ValidInTransitMsg ==
  /\ \A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : m.source = snder
  /\ \A snder, rcver \in Proc : \A m1, m2 \in inTransit[snder][rcver] : 
        (    ( /\ m1.id = m2.id
               /\ m1.type = MType
               /\ m2.type = PType )
          => m1.t < m2.t)            
      
 
ValidInTransitProposeTS ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc : \A m \in inTransit[snder][rcver] : m.id # id )
  /\ ( \A id \in McastID : \A snder \in Proc \ GroupDest[id] : \A rcver \in Proc : \A m \in inTransit[snder][rcver] : m.id # id )
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A snder \in Proc : \A m \in inTransit[snder][rcver] : 
              ( /\ m.id = id 
                /\ m.source = snder                
                /\ m.type = PType ) 
          =>  ( /\ m.t = localTS[snder][id].t 
                /\ id \in rcvdMcastID[snder] 
                /\ id \in mcastedID ) )            
  /\ (\A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : m.t <= clock[m.source] /\ m.t > TimeNull)      
  /\ (\A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : 
          m.t = PType => ( /\ globalTS[rcver][m.id] = TimestampNull
                           \*/\ ~(\E m1 \in inTransit[McastID[m.id]][snder] : m1.id = m.id /\ m1.type = MType)
                           \*/\ ~(\E p \in Proc : \E m1 \in inTransit[p][snder] : p = McastID[m.id] /\ m1.id = m.id /\ m1.type = MType)
                           /\ localTS[m.source][m.id] # TimestampNull
                           /\ m.id \in rcvdMcastID[m.source]))                           
  /\ (\A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : 
          m.t = PType => ( /\ localTS[m.source][m.id].g = m.source
                           /\ localTS[m.source][m.id].t = m.t ))                           
  /\ (\A id \in McastID : \A snder, rcver \in GroupDest[id] : \A m \in inTransit[snder][rcver] :                                                                  
            ((m.t = PType /\ m.id = id) 
                =>  (\A m1 \in inTransit[Mcaster[id]][snder] : m1.type = MType => m1.id # id)))
(*      
ValidRcvdProposeTS ==
  \A rcver \in Proc : \A id \in McastID :
      IF rcver \notin GroupDest[id]
      THEN \A snder \in Proc : proposeTS[rcver][snder][id] = TimestampNull
      ELSE \A snder \in Proc : proposeTS[rcver][snder][id] # TimestampNull  
                                  => ( /\ proposeTS[rcver][snder][id] = localTS[snder][id]
                                       /\ \A m \in inTransit[snder][rcver] : m.id # id )
 *)
ValidRcvdProposeTS1 ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc : 
          proposeTS[rcver][id] = ({} <: {[type |-> Int, t |-> Int, id |-> Int, source |-> Int]} ))
          
ValidRcvdProposeTS2 ==                    
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A msg \in proposeTS[rcver][id] :
          /\ msg.t = localTS[msg.source][msg.id].t
          /\ msg.id = id
          /\ (\A m \in inTransit[msg.source][rcver] : m.id # id ) )
          
ValidRcvdProposeTS3 ==                    
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A msg \in proposeTS[rcver][id] : 
          /\ msg.t = localTS[msg.source][msg.id].t
          /\ msg.source = localTS[msg.source][msg.id].g
          /\ msg.id = id )

  
ValidRcvdProposeTS ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc : 
          proposeTS[rcver][id] = ({} <: {[type |-> Int, t |-> Int, id |-> Int, source |-> Int]} ))          
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A msg \in proposeTS[rcver][id] :
          /\ msg.t = localTS[msg.source][msg.id].t
          /\ msg.id = id
          /\ (\A m \in inTransit[msg.source][rcver] : m.id # id ) )          
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A msg \in proposeTS[rcver][id] : 
          /\ msg.t = localTS[msg.source][msg.id].t
          /\ msg.source = localTS[msg.source][msg.id].g
          /\ msg.id = id )
  
                  
BoundedClock == \A p \in Proc : clock[p] <= MaxClock

ValidGlobalTS ==
  /\ \A id \in McastID : \A rcver \in GroupDest[id] :  
        ( globalTS[rcver][id] # TimestampNull
            <=> ( /\ \A snder \in GroupDest[id] : \E m \in proposeTS[rcver][id] : 
                        ( /\ m.source = snder 
                          /\ \/ m.t < globalTS[rcver][id].t
                             \/ /\ m.t = globalTS[rcver][id].t
                                /\ m.source <= globalTS[rcver][id].g ) )                         
                  /\ \E snder \in GroupDest[id] : \E m \in proposeTS[rcver][id] :
                        ( /\ globalTS[rcver][id].t = m.t
                          /\ globalTS[rcver][id].g = m.source ) )                        
  /\ \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : globalTS[rcver][id] = TimestampNull
  /\ \A id \in McastID : \A rcver \in GroupDest[id] : globalTS[rcver][id].g # GroupNull => globalTS[rcver][id].t # TimeNull
  /\ \A id \in McastID : \A p \in Proc \ GroupDest[id] : globalTS[p][id] = TimestampNull
  /\ \A id \in McastID : \A p \in GroupDest[id] : 
        globalTS[p][id] # TimestampNull => \E q \in GroupDest[id] : localTS[q][id] = globalTS[p][id]                   
  /\ \A id \in McastID : \A rcver \in GroupDest[id] : globalTS[rcver][id].g # GroupNull => globalTS[rcver][id].t <= clock[rcver]        
                  
ValidPhase ==
  \A p \in Proc : \A id \in McastID :
    ( /\ p \notin GroupDest[id] => phase[p][id] = Start
      /\ phase[p][id] = Start <=> localTS[p][id] = TimestampNull
      /\ phase[p][id] = Proposed => (localTS[p][id] # TimestampNull /\ id \in rcvdMcastID[p])
      /\ phase[p][id] = Committed <=> (\A q \in GroupDest[id] : \E m \in proposeTS[p][id] : m.source = q )
      /\ (localTS[p][id] # TimestampNull /\ id \in rcvdMcastID[p]) => phase[p][id] \in {Proposed, Committed} )
                  
ValidDelivery ==
  \A p \in Proc : \A id \in McastID :
        delivered[p][id] 
    => ( /\ globalTS[p][id] # TimestampNull 
         /\ phase[p][id] = Committed
         /\ \A mid \in rcvdMcastID[p] : 
                phase[p][mid] = Proposed => Less(globalTS[p][id], localTS[p][mid]) )                 

UniqueMsg1 ==
  \A snder, rcver \in Proc : \A m1, m2 \in inTransit[snder][rcver] :
          /\ ( m1.type = m2.type /\ m1.id = m2.id) => m1.t = m2.t

UniqueMsg2 ==
  \A snder, rcver \in Proc : \A m1, m2 \in inTransit[snder][rcver] :
          /\ ( m1.type = m2.type /\ m1.t  = m2.t) => m1.id = m2.id 

UniqueMsg3 ==
  \A snder, rcver \in Proc : \A m1, m2 \in inTransit[snder][rcver] :
          /\ ( m1.id   = m2.id   /\ m1.t  = m2.t)  => m1.type = m2.type 

UniqueMsg4 ==
  \A m \in inTransit :  
      m.type = PType => ~( \E m1 \in inTransit : /\ m1.id = m.id 
                                                 /\ m1.source = Mcaster[m.id]                                                 
                                                 /\ m1.type = MType )                                                    

                  
UniqueMsg ==
  /\ ( \A snder, rcver \in Proc : \A m1, m2 \in inTransit[snder][rcver] :
          /\ ( m1.type = m2.type /\ m1.id = m2.id) => m1.t = m2.t
          /\ ( m1.type = m2.type /\ m1.t  = m2.t)  => m1.id = m2.id
          /\ ( m1.id   = m2.id   /\ m1.t  = m2.t)  => m1.type = m2.type )
  /\ ( \A snder, rcver \in Proc :\A m \in inTransit[snder][rcver] :  
               m.type = PType => ~( \E m1 \in inTransit[Mcaster[m.id]][snder] : 
                                            /\ m1.id = m.id 
                                            /\ m1.source = Mcaster[m.id]                                            
                                            /\ m1.type = MType ) )                                                    
                                                           
ValidInTransitMcast1 ==
  /\ \A snder, rcver \in Proc : \A id \in McastID : \A m \in inTransit[snder][rcver] :
        (m.type = MType /\ m.id = id) => (snder = Mcaster[id] /\ id \in mcastedID)
        
ValidInTransitMcast2 ==        
  /\ \A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : 
        m.type = MType => m.source = Mcaster[m.id]
  
ValidInTransitMcast3 ==   
  /\ \A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : 
        m.type = MType => m.id \in mcastedID     
     
             
ValidInTransitMcast ==
  /\ \A snder, rcver \in Proc : \A id \in McastID : \A m \in inTransit[snder][rcver] :
        (m.type = MType /\ m.id = id) => (snder = Mcaster[id] /\ id \in mcastedID)
  /\ \A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : 
        m.type = MType => m.source = Mcaster[m.id]
  /\ \A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : 
        m.type = MType => m.id \in mcastedID         
  /\ \A snder, rcver \in Proc : \A m \in inTransit[snder][rcver] : 
        m.t <= clock[m.source] /\ m.t > TimeNull
  /\ \A mcaster, rcver \in Proc : \A m \in inTransit[mcaster][rcver] : 
        m.type = MType => ( /\ ~(\E q \in Proc : \E m1 \in inTransit[rcver][q] : m1.source = rcver /\ m1.id = m.id /\ m1.type = PType)
                            /\ localTS[rcver][m.id] = TimestampNull
                            /\ \A p \in GroupDest[m.id] : globalTS[p][m.id] = TimestampNull)
    
TypeOK1 ==
  /\ rcvdMcastID \in [Proc -> SUBSET McastID]
  /\ mcastedID \in SUBSET McastID   
  
TypeOK3 ==  
  /\ inTransit \in  SUBSET InTransitMsgSet  
  
TypeOK4 ==  
  /\ delivered \in [Proc -> [McastID -> BOOLEAN]]
  
TypeOK5 ==   
  /\ proposeTS \in [Proc -> [McastID -> SUBSET ProposeMsgSet]]
    
TypeOK2 ==
  /\ clock \in [Proc -> Time \cup {TimeNull}]
  /\ localTS \in [Proc -> [McastID -> TimestampSet]]   
  /\ globalTS \in [Proc -> [McastID -> TimestampSet]]   
  /\ phase \in [Proc -> [McastID -> {Start, Proposed, Committed}]]  
  /\ rcvdMcastID \in [Proc -> SUBSET McastID]
  

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
  
NeverCommit ==
  \A p \in Proc : \A id \in McastID : phase[p][id] # Committed     
  
Termination ==
  <>(\A id \in McastID : \A p \in GroupDest[id] : delivered[p][id])  
  
IndInv ==
  /\ TypeOK
  /\ ValidInTransitMsg  
  /\ Validity
  /\ AsymmetricOrdering
  /\ ConsistentGlobalTS
  /\ ValidOwnedLocalTS 
  /\ ValidInTransitProposeTS  
  /\ ValidRcvdProposeTS
  /\ BoundedClock  
  /\ ValidGlobalTS                    
  /\ ValidDelivery
  /\ ValidPhase 
  /\ ValidInTransitMcast  
  /\ UniqueMsg
    
    
(* Initial state *)
State0 ==
  clock = 1 :> 1 @@ 2 :> 5
    /\ delivered
      = 1 :> (1 :> FALSE @@ 2 :> FALSE) @@ 2 :> (1 :> FALSE @@ 2 :> FALSE)
    /\ globalTS
      = 1 :> (1 :> [g |-> 0, t |-> 0] @@ 2 :> [g |-> 0, t |-> 0])
        @@ 2 :> (1 :> [g |-> 0, t |-> 0] @@ 2 :> [g |-> 0, t |-> 0])
    /\ inTransit
      = 1 :> (1 :> {} @@ 2 :> {})
        @@ 2
          :> (1
              :> { [id |-> 2, source |-> 2, t |-> 4, type |-> 11],
                [id |-> 2, source |-> 2, t |-> 5, type |-> 10] }
            @@ 2 :> {})
    /\ localTS
      = 1 :> (1 :> [g |-> 1, t |-> 1] @@ 2 :> [g |-> 0, t |-> 0])
        @@ 2 :> (1 :> [g |-> 2, t |-> 5] @@ 2 :> [g |-> 2, t |-> 4])
    /\ mcastedID = { 1, 2 }
    /\ phase = 1 :> (1 :> 13 @@ 2 :> 12) @@ 2 :> (1 :> 13 @@ 2 :> 13)
    /\ proposeTS
      = 1 :> (1 :> {[id |-> 1, source |-> 2, t |-> 5, type |-> 11]} @@ 2 :> {})
        @@ 2
          :> (1 :> {[id |-> 1, source |-> 1, t |-> 1, type |-> 11]}
            @@ 2 :> {[id |-> 2, source |-> 2, t |-> 4, type |-> 11]})
    /\ rcvdMcastID = 1 :> {1} @@ 2 :> { 1, 2 }

(* Transition 4 to State1 *)
State1 ==
  clock = 1 :> 1 @@ 2 :> 5
    /\ delivered
      = 1 :> (1 :> FALSE @@ 2 :> FALSE) @@ 2 :> (1 :> FALSE @@ 2 :> FALSE)
    /\ globalTS
      = 1 :> (1 :> [g |-> 0, t |-> 0] @@ 2 :> [g |-> 0, t |-> 0])
        @@ 2 :> (1 :> [g |-> 0, t |-> 0] @@ 2 :> [g |-> 0, t |-> 0])
    /\ inTransit
      = 1 :> (1 :> {} @@ 2 :> {})
        @@ 2
          :> (1 :> {[id |-> 2, source |-> 2, t |-> 5, type |-> 10]} @@ 2 :> {})
    /\ localTS
      = 1 :> (1 :> [g |-> 1, t |-> 1] @@ 2 :> [g |-> 0, t |-> 0])
        @@ 2 :> (1 :> [g |-> 2, t |-> 5] @@ 2 :> [g |-> 2, t |-> 4])
    /\ mcastedID = { 1, 2 }
    /\ phase = 1 :> (1 :> 13 @@ 2 :> 12) @@ 2 :> (1 :> 13 @@ 2 :> 13)
    /\ proposeTS
      = 1
          :> (1 :> {[id |-> 1, source |-> 2, t |-> 5, type |-> 11]}
            @@ 2 :> {[id |-> 2, source |-> 2, t |-> 4, type |-> 11]})
        @@ 2
          :> (1 :> {[id |-> 1, source |-> 1, t |-> 1, type |-> 11]}
            @@ 2 :> {[id |-> 2, source |-> 2, t |-> 4, type |-> 11]})
    /\ rcvdMcastID = 1 :> {1} @@ 2 :> { 1, 2 }    


=============================================================================
\* Modification History
\* Last modified Mon Mar 22 12:06:38 CET 2021 by tran
\* Created Tue Mar 16 08:59:43 CET 2021 by tran
