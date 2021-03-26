-------------------------------- MODULE iinv --------------------------------

EXTENDS skeen

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
  
Integrity ==
  \A id \in McastID : \A p \in Proc : 
      /\ delivered[p][id] <=> dCntr[p][id] = 1  
      /\ ~delivered[p][id] <=> dCntr[p][id] = 0
  
IndInv ==
  /\ TypeOK
  /\ Integrity


=============================================================================
\* Modification History
\* Last modified Thu Mar 25 20:37:39 CET 2021 by tran
\* Created Thu Mar 25 20:37:25 CET 2021 by tran
