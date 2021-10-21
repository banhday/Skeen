-------------------------------- MODULE iinv --------------------------------

EXTENDS skeen_v3

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

TypeOKIndInv == TypeOK /\ IndInv

=============================================================================
\* Modification History
\* Last modified Thu Mar 25 20:37:39 CET 2021 by tran
\* Created Thu Mar 25 20:37:25 CET 2021 by tran
