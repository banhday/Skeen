------------------------------- MODULE vinv -------------------------------

EXTENDS skeen

Integrity ==
  \A id \in McastID : \A p \in Proc : 
      /\ delivered[p][id] <=> dCntr[p][id] = 1  
      /\ ~delivered[p][id] <=> dCntr[p][id] = 0

Validity == \A p \in Proc : \A id \in McastID : delivered[p][id] => id \in mcastedID


\* If process p is not an addressee of message id, p never issues a local timestamp for id.
\* The owner of the local timestamp localTS[p][id] must be process p. 
ValidOwnedLocalTS ==
  /\ ( \A id \in McastID : \A p \in Proc \ GroupDest[id] : localTS[p][id] = TimestampNull )
  /\ ( \A id \in McastID : \A p \in GroupDest[id] :
          (localTS[p][id] # TimestampNull 
                => ( /\ id \in mcastedID
                     /\ localTS[p][id].g = p ))) 
      
      
\* If process p is not an addressee of message id, no processes send a proposal for message id to process p.
\* If process p is not an addressee of message id, it never sends a proposal for message id.
\* If there exists a proposal for message id, message id must be multicast before.
ValidInTransitProposeTS ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc :  
            \A m \in inTransit[snder][rcver] : m.id # id )
  /\ ( \A id \in McastID : \A snder \in Proc \ GroupDest[id] : \A rcver \in Proc : 
            \A m \in inTransit[snder][rcver] : m.id # id )
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A snder \in Proc :  
            \A m \in inTransit[snder][rcver] : m.id = id => id \in mcastedID)            
  
\* If process p is not an addressee of message id, it never receives any a proposal for message id.  
\* If process p has received a proposal for message id, message id must be multicast before.
ValidRcvdProposeTS ==
  /\ ( \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : \A snder \in Proc : 
          proposeTS[rcver][id] = ({} <: {[type |-> Int, t |-> Int, id |-> Int, source |-> Int]} ))          
  /\ ( \A id \in McastID : \A rcver \in GroupDest[id] : \A msg \in proposeTS[rcver][id] :
          /\ msg.id \in mcastedID )
  
\* Every local clock is bounded with MaxClock                  
BoundedClock == \A p \in Proc : clock[p] <= MaxClock


\* If process p issues a global timestamp for message id, message id must be multicast before. 
\* If process p is not an addressee of message id, t never issues a global timestamp for message id.
ValidGlobalTS ==
  /\ \A id \in McastID : \A rcver \in GroupDest[id] :  
          globalTS[rcver][id] # TimestampNull => id \in mcastedID                        
  /\ \A id \in McastID : \A rcver \in Proc \ GroupDest[id] : 
          globalTS[rcver][id] = TimestampNull
                  
                                                               
\* If there exists an in-transit multicast message for message id, message id must be multicast before by
\* its multicaster.              
ValidInTransitMcast ==
  /\ \A snder, rcver \in Proc : \A id \in McastID : \A m \in inTransit[snder][rcver] :
        (m.type = MType /\ m.id = id) => (snder = Mcaster[id] /\ id \in mcastedID)
    
  
\* Type invariants
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
  /\ dCntr \in [Proc -> [McastID -> {0, 1}]]
  
  
\* If process p commits message id, it has received at least one proposal for message id.
\* If process p commits message id, it has not issued any global timestamp for message id.   
ValidPhase ==
  \A p \in Proc : \A id \in McastID :
    ( /\ phase[p][id] = Committed => (\A q \in GroupDest[id] : \E m \in proposeTS[p][id] : m.source = q )
      /\ phase[p][id] = Committed => globalTS[p][id] # TimestampNull)
                  
\* This inductive invariant implies Validity.  
IndInv ==
  /\ TypeOK   
  /\ Validity
  /\ Integrity
  /\ ValidOwnedLocalTS 
  /\ ValidInTransitProposeTS  
  /\ ValidRcvdProposeTS
  /\ BoundedClock  
  /\ ValidGlobalTS                     
  /\ ValidInTransitMcast  
  /\ ValidPhase
  


=============================================================================
\* Modification History
\* Last modified Mon Sep 20 16:51:56 CEST 2021 by tran
\* Created Tue Mar 16 08:59:43 CET 2021 by tran
