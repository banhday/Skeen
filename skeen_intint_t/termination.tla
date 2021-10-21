---------------------------- MODULE termination ----------------------------

EXTENDS skeen_v3

\* If message id is multicast by a process, then every addressee of message m eventually delivers m.
Termination ==
  <>(\A id \in McastID : \A p \in GroupDest[id] : delivered[<< p, id >>])  

=============================================================================
\* Modification History
\* Last modified Thu Mar 25 22:11:02 CET 2021 by tran
\* Created Thu Mar 25 20:29:19 CET 2021 by tran
