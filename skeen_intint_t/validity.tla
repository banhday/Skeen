------------------------------ MODULE validity ------------------------------

EXTENDS skeen_v3

\* If process p delivers message id, then some process has multicast message id before, 
\* and p is one of addressees of message id
Validity == \A p \in Proc : \A id \in McastID : delivered[<< p, id >>] => id \in mcastedID

=============================================================================
\* Modification History
\* Last modified Thu Mar 25 22:11:48 CET 2021 by tran
\* Created Thu Mar 25 18:30:24 CET 2021 by tran
