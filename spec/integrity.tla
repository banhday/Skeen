----------------------------- MODULE integrity -----------------------------

EXTENDS skeen

\* Every process delivers a message at most once.
Integrity ==
  \A id \in McastID : \A p \in Proc : 
      /\ delivered[p][id] <=> dCntr[p][id] = 1  
      /\ ~delivered[p][id] <=> dCntr[p][id] = 0


=============================================================================
\* Modification History
\* Last modified Thu Mar 25 22:12:08 CET 2021 by tran
\* Created Thu Mar 25 18:41:14 CET 2021 by tran
