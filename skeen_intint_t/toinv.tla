------------------------------- MODULE toinv -------------------------------

EXTENDS skeen_v3

(*

  - Total Order: There exists a total order < on all messages that are multicast
                 in an execution trace such that, if process p delivers message m, then for all
                 messages m' < m such that p is one of addresses of message m', p delivers m' before m.
  - Total Order can be formalized as the following formula

    GlobalTotalOrdering ==
      \E ordering \in [McastID -> 1..M] : 
          /\ \A p \in Proc : \A id1, id2 \in McastID : 
                ( /\ globalTS[<< p, id1 >>] # TimestampNull
                  /\ globalTS[<< p, id2 >>] # TimestampNull
                  /\ ordering[id1] < ordering[id2] )
                        => Less(globalTS[<< p, id1 >>], globalTS[<< p, id2 >>])

  - However, APALACHE cannot verify GlobalTotalOrdering because the initialization of ordering and
    its corresponding quantifiers. 
 *)
    
\* The conjunction of ConsistentGlobalTS and AsymmetricOrdering implies Total Order 
AsymmetricOrdering == 
  \A id1, id2 \in McastID : \A p, q \in Proc :
      ( /\ globalTS[<< p, id1 >>] # TimestampNull 
        /\ globalTS[<< p, id2 >>] # TimestampNull 
        /\ globalTS[<< q, id1 >>] # TimestampNull 
        /\ globalTS[<< q, id2 >>] # TimestampNull
        /\ id1 # id2 )
            => ~(Less(globalTS[<< p, id1 >>], globalTS[<< p, id2 >>]) /\ Less(globalTS[<< q, id2 >>], globalTS[<< q, id1 >>]))
 
 
ConsistentGlobalTS ==  
  /\ \A id \in McastID : \A p, q \in Proc :             \* All addressees of message id must agree on its global timestamp.
      ( /\ globalTS[<< p, id >>] # TimestampNull              
        /\ globalTS[<< q, id >>] # TimestampNull )
            => globalTS[<< p, id >>] = globalTS[<< q, id >>]        
  /\ \A id1, id2 \in McastID : \A p \in Proc :          \* Every message has a unique global timestamp.
      ( /\ id1 # id2
        /\ globalTS[<< p, id1 >>] # TimestampNull         
        /\ globalTS[<< p, id2 >>] # TimestampNull )
            => globalTS[<< p, id1 >>] # globalTS[<< p, id2 >>]      



Validity == \A p \in Proc : \A id \in McastID : delivered[<< p, id >>] => id \in mcastedID



\* If process p is not an addressee of message id, p never issues a local timestamp for id.
\* Process p issues a local timestampe for message id if and only if it receive a multicast message for id.
\* The time in every local timestamp cannot greater than the current value of the local clock.
\* Never issues a local timestamp with GroupNull or TimestampNull.
\* The owner of the local timestamp localTS[<< p, id >>] must be process p. 
\* Never issues two local timestapms at one time point.
ValidOwnedLocalTS ==
  
  /\ ( \A id \in McastID : \A p \in Proc \ GroupDest[id] : localTS[<< p, id >>] = TimestampNull )
  /\ ( \A id \in McastID : \A p \in GroupDest[id] :
          /\ localTS[<< p, id >>] = TimestampNull <=> id \notin rcvdMcastID[p]
          /\ localTS[<< p, id >>].t <= clock[p]
          /\ (localTS[<< p, id >>].g # GroupNull => localTS[<< p, id >>].t # TimeNull)
          /\ (localTS[<< p, id >>] # TimestampNull 
                => ( /\ id \in mcastedID
                     /\ localTS[<< p, id >>].g = p ))) 
  /\ \A id1, id2 \in McastID : \A p \in Proc :
        ((  /\ p \in GroupDest[id1] 
            /\ p \in GroupDest[id2]
            /\ id1 # id2
            /\ localTS[<< p, id1 >>] # TimestampNull
            /\ localTS[<< p, id2 >>] # TimestampNull )
                  => localTS[<< p, id1 >>].t # localTS[<< p, id2 >>].t )                     


\* Every in-transit message in inTransit[<< snder, rcver >>] was sent by process snder.
\* The in-transit proposed message for message id must be sent after the multicast message for message id.
ValidInTransitMsg ==
  /\ \A snder, rcver \in Proc : \A m \in inTransit[<< snder, rcver >>] : m.source = snder
  /\ \A snder, rcver \in Proc : \A m1, m2 \in inTransit[<< snder, rcver >>] : 
        (    ( /\ m1.id = m2.id
               /\ m1.type = MType
               /\ m2.type = PType )
          => m1.t < m2.t)            
      
(* 
  - If process p is not an addressee of message id, no processes send a proposal for message id to process p.
  - If process p is not an addressee of message id, it never sends a proposal for message id.
  - If there exists a proposal for message id from process snder, process snder has issued a local timestamp 
    for message m. These timestamps must be the same.
  - If there exists a proposal for message id, message id must be multicast before.
  - The time in an issued timestamp by process snder cannot greater than the current value of the clock of process snder.
  - If there exists an in-transit proposed message for message id that is sent to process rcver,
    process rcver has not issued a global timestamp for message id.
  - If there exists an in-transit proposed message for message id that is sent from process snder,
    process snder has issued a local timestamp for message id.    
  - If there exists an in-transit proposed message for message id, message id must be multicast before.
  - If there exists an in-transit proposed message for message id that is sent from process snder,
    there exists no in-transit multicast message to process snder such that this multicast message is for
    message id.    
 *)
ValidInTransitProposeTS ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc : \A m \in inTransit[<< snder, rcver >>] : m.id # id )
  /\ ( \A id \in McastID : \A snder \in Proc \ GroupDest[id] : \A rcver \in Proc : \A m \in inTransit[<< snder, rcver >>] : m.id # id )
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A snder \in Proc : \A m \in inTransit[<< snder, rcver >>] : 
              ( /\ m.id = id 
                /\ m.source = snder                
                /\ m.type = PType ) 
          =>  ( /\ m.t = localTS[<< snder, id >>].t 
                /\ id \in rcvdMcastID[snder] 
                /\ id \in mcastedID ) )            
  /\ (\A snder, rcver \in Proc : \A m \in inTransit[<< snder, rcver >>] : m.t <= clock[m.source] /\ m.t > TimeNull)      
  /\ (\A snder, rcver \in Proc : \A m \in inTransit[<< snder, rcver >>] : 
          m.t = PType => ( /\ globalTS[<< rcver, m.id >>] = TimestampNull
                           \*/\ ~(\E m1 \in inTransit[<< McastID[m.id], snder >>] : m1.id = m.id /\ m1.type = MType)
                           \*/\ ~(\E p \in Proc : \E m1 \in inTransit[<< p, snder >>] : p = McastID[m.id] /\ m1.id = m.id /\ m1.type = MType)
                           /\ localTS[<< m.source, m.id >>] # TimestampNull
                           /\ m.id \in rcvdMcastID[m.source]))                           
  /\ (\A snder, rcver \in Proc : \A m \in inTransit[<< snder, rcver >>] : 
          m.t = PType => ( /\ localTS[<< m.source, m.id >>].g = m.source
                           /\ localTS[<< m.source, m.id >>].t = m.t ))                           
  /\ (\A id \in McastID : \A snder, rcver \in GroupDest[id] : \A m \in inTransit[<< snder, rcver >>] :                                                                  
            ((m.t = PType /\ m.id = id) 
                =>  (\A m1 \in inTransit[<< Mcaster[id], snder >>] : m1.type = MType => m1.id # id)))


(* 
  - If process p is not an addressee of message id, it never receives a proposal for message id.
  - Every received proposed message for message id must be grouped correctly.
  - Every received proposed message for message id from process snder must propose the local timestamp that
    is issued by process snder for message id.
 *) 
ValidRcvdProposeTS ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc : 
          proposeTS[<< rcver, id >>] = {} )          
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A msg \in proposeTS[<< rcver, id >>] :
          /\ msg.t = localTS[<< msg.source, msg.id >>].t
          /\ msg.id = id
          /\ (\A m \in inTransit[<< msg.source, rcver >>] : m.id # id ) )          
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A msg \in proposeTS[<< rcver, id >>] : 
          /\ msg.t = localTS[<< msg.source, msg.id >>].t
          /\ msg.source = localTS[<< msg.source, msg.id >>].g
          /\ msg.id = id )
  
\* Every local clock is bounded with MaxClock                                    
BoundedClock == \A p \in Proc : clock[p] <= MaxClock

(*   
  - The global timestamp for message m cannot be less than any proposed local timestamp for message m.
  - The global timestamp for message m must equal some local timestamp for message m.
  - If process p is not an addressee of message id, it never issues a global timestamp for message id.  
  - There exists no global timestamp with GroupNull or TimeNull.
  - The time in every global timestamp cannot greater than the current value of the clock.
  - The global timestamp for message id is issued if and only if message id is committed.
 *)
ValidGlobalTS ==
  /\ \A id \in McastID : \A rcver \in GroupDest[id] :  
        ( globalTS[<< rcver, id >>] # TimestampNull
            <=> ( /\ \A snder \in GroupDest[id] : \E m \in proposeTS[<< rcver, id >>] : 
                        ( /\ m.source = snder 
                          /\ \/ m.t < globalTS[<< rcver, id >>].t
                             \/ /\ m.t = globalTS[<< rcver, id >>].t
                                /\ m.source <= globalTS[<< rcver, id >>].g ) )                         
                  /\ \E snder \in GroupDest[id] : \E m \in proposeTS[<< rcver, id >>] :
                        ( /\ globalTS[<< rcver, id >>].t = m.t
                          /\ globalTS[<< rcver, id >>].g = m.source ) )                        
  /\ \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : globalTS[<< rcver, id >>] = TimestampNull
  /\ \A id \in McastID : \A rcver \in GroupDest[id] : globalTS[<< rcver, id >>].g # GroupNull => globalTS[<< rcver, id >>].t # TimeNull
  /\ \A id \in McastID : \A p \in Proc \ GroupDest[id] : globalTS[<< p, id >>] = TimestampNull
  /\ \A id \in McastID : \A p \in GroupDest[id] : 
        globalTS[<< p, id >>] # TimestampNull => \E q \in GroupDest[id] : localTS[<< q, id >>] = globalTS[<< p, id >>]                   
  /\ \A id \in McastID : \A rcver \in GroupDest[id] : globalTS[<< rcver, id >>].g # GroupNull => globalTS[<< rcver, id >>].t <= clock[rcver]        
  /\ \A id \in McastID : \A p \in Proc : globalTS[<< p, id >>] # TimestampNull <=> phase[<< p, id >>] = Committed  

\* Process p sets the status of message id to Start iff it has not issued a local timestamp for message id.
\* If process p commits message id, it has received at least one proposal for message id.
\* If process p commits message id, it has not issued any global timestamp for message id.                     
ValidPhase ==
  \A p \in Proc : \A id \in McastID :
    ( /\ p \notin GroupDest[id] => phase[<< p, id >>] = Start
      /\ phase[<< p, id >>] = Start <=> localTS[<< p, id >>] = TimestampNull
      /\ phase[<< p, id >>] = Proposed => (localTS[<< p, id >>] # TimestampNull /\ id \in rcvdMcastID[p])
      /\ phase[<< p, id >>] = Committed <=> (\A q \in GroupDest[id] : \E m \in proposeTS[<< p, id >>] : m.source = q )
      /\ (localTS[<< p, id >>] # TimestampNull /\ id \in rcvdMcastID[p]) => phase[<< p, id >>] \in {Proposed, Committed} )
                  

\* Message id can be delivered to process p if and only if process p has issued a global timestamp for message id
\* and the local timestamps of all proposed message at process p must be greater than the global timestamp of message id.
ValidDelivery ==
  \A p \in Proc : \A id \in McastID :
        delivered[<< p, id >>] 
    => ( /\ globalTS[<< p, id >>] # TimestampNull 
         /\ phase[<< p, id >>] = Committed
         /\ \A mid \in rcvdMcastID[p] : 
                phase[<< p, mid >>] = Proposed => Less(globalTS[<< p, id >>], localTS[<< p, mid >>]) )                 

                                                  

\* Every in-transit message has an unique timestamp.
\* If process snder has sent a proposal for message id, no in-transit message to process p is a multicast
\* message for message id.
UniqueMsg ==
  /\ ( \A snder, rcver \in Proc : \A m1, m2 \in inTransit[<< snder, rcver >>] :
          /\ ( m1.type = m2.type /\ m1.id = m2.id) => m1.t = m2.t
          /\ ( m1.type = m2.type /\ m1.t  = m2.t)  => m1.id = m2.id
          /\ ( m1.id   = m2.id   /\ m1.t  = m2.t)  => m1.type = m2.type )
  /\ ( \A snder, rcver \in Proc :\A m \in inTransit[<< snder, rcver >>] :  
               m.type = PType => ~( \E m1 \in inTransit[<< Mcaster[m.id], snder >>] : 
                                            /\ m1.id = m.id 
                                            /\ m1.source = Mcaster[m.id]                                            
                                            /\ m1.type = MType ) )                                                    
                                                           
   
(*
  - If process p is not an addressee of message id, it never receives a multicast message for message id.
  - Every multicast message for message id must be multicast by its multicaster.
  - If there exists a multicast message for message id, message id must be multicast before.
  - The timestamp of every proposed message from process snder cannot be greater the local clock
    of process snder, and must be not 0.
  - If there exists an in-transit multicast message for message id to process rcver, process rcver has not issued
    neither local timestamp nor global timestamp for message id.
 *)
ValidInTransitMcast ==
  /\ \A snder, rcver \in Proc : \A id \in McastID : \A m \in inTransit[<< snder, rcver >>] :
        (m.type = MType /\ m.id = id) => (snder = Mcaster[id] /\ id \in mcastedID)
  /\ \A snder, rcver \in Proc : \A m \in inTransit[<< snder, rcver >>] : 
        m.type = MType => m.source = Mcaster[m.id]
  /\ \A snder, rcver \in Proc : \A m \in inTransit[<< snder, rcver >>] : 
        m.type = MType => m.id \in mcastedID         
  /\ \A snder, rcver \in Proc : \A m \in inTransit[<< snder, rcver >>] : 
        m.t <= clock[m.source] /\ m.t > TimeNull
  /\ \A mcaster, rcver \in Proc : \A m \in inTransit[<< mcaster, rcver >>] : 
        m.type = MType => ( /\ ~(\E q \in Proc : \E m1 \in inTransit[<< rcver, q >>] : m1.source = rcver /\ m1.id = m.id /\ m1.type = PType)
                            /\ localTS[<< rcver, m.id >>] = TimestampNull
                            /\ \A p \in GroupDest[m.id] : globalTS[<< p, m.id >>] = TimestampNull)   
  

TypeOK ==
  /\ clock \in [Proc -> Time \cup {TimeNull}]
  /\ localTS \in [(Proc \times McastID) -> TimestampSet]   
  /\ globalTS \in [(Proc \times McastID) -> TimestampSet]   
  /\ phase \in [(Proc \times McastID) -> {Start, Proposed, Committed}]  
  /\ rcvdMcastID \in [Proc -> SUBSET McastID]
  /\ mcastedID \in SUBSET McastID   
  /\ inTransit \in [(Proc \times Proc) -> SUBSET InTransitMsgSet]  
  /\ delivered \in [(Proc \times McastID) -> BOOLEAN] 
  /\ proposeTS \in [(Proc \times McastID) -> SUBSET ProposeMsgSet]
  /\ dCntr \in [Proc \times McastID -> {0, 1}]   

  
Integrity ==
  \A id \in McastID : \A p \in Proc : 
      /\ delivered[<< p, id >>] <=> dCntr[<< p, id >>] = 1  
      /\ ~delivered[<< p, id >>] <=> dCntr[<< p, id >>] = 0
  

IndInv ==
  /\ Integrity
  /\ Validity  
  /\ ValidInTransitMsg  
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
    
    
TypeOKIndInv == TypeOK /\ IndInv    

=============================================================================
\* Modification History
\* Last modified Mon Mar 22 12:06:38 CET 2021 by tran
\* Created Tue Mar 16 08:59:43 CET 2021 by tran
