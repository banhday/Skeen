---------------------------- MODULE total_order ----------------------------

EXTENDS skeen

(*
  - Total Order: There exists a total order < on all messages that are multicast
                 in an execution trace such that, if process p delivers message m, then for all
                 messages m' < m such that p is one of addresses of message m', p delivers m' before m.
  - Total Order can be formalized as the following formula
    
    GlobalTotalOrdering ==
        \E ordering \in [McastID -> 1..M] :
            /\ \A id1, id2 \in McastID : ordering[id1] = ordering[id2] => id1 = id2
            /\ \A p \in Proc : \A id1, id2 \in McastID : 
                  ( /\ globalTS[p][id1] # TimestampNull
                    /\ globalTS[p][id2] # TimestampNull
                    /\ ordering[id1] < ordering[id2] )
                          => Less(globalTS[p][id1], globalTS[p][id2])
                          
  - However, APALACHE cannot verify GlobalTotalOrdering because the initialization of ordering and
    its corresponding quantifiers.                                    
 *)                 


\* The conjunction of ConsistentGlobalTS and AsymmetricOrdering implies Total Order 
ConsistentGlobalTS ==  
  /\ \A id \in McastID : \A p, q \in Proc :             \* All addressees of message id must agree on its global timestamp.
      ( /\ globalTS[p][id] # TimestampNull         
        /\ globalTS[q][id] # TimestampNull )
            => globalTS[p][id] = globalTS[q][id]        
  /\ \A id1, id2 \in McastID : \A p \in Proc :          \* Every message has a unique global timestamp.
      ( /\ id1 # id2
        /\ globalTS[p][id1] # TimestampNull         
        /\ globalTS[p][id2] # TimestampNull )
            => globalTS[p][id1] # globalTS[p][id2]      

AsymmetricOrdering == 
  \A id1, id2 \in McastID : \A p, q \in Proc :
      ( /\ globalTS[p][id1] # TimestampNull 
        /\ globalTS[p][id2] # TimestampNull 
        /\ globalTS[q][id1] # TimestampNull 
        /\ globalTS[q][id2] # TimestampNull             \* The global timestamps of messages preserve asymmetric order. 
        /\ id1 # id2 )
            => ~(Less(globalTS[p][id1], globalTS[p][id2]) /\ Less(globalTS[q][id2], globalTS[q][id1]))
=============================================================================
\* Modification History
\* Last modified Thu Mar 25 22:17:11 CET 2021 by tran
\* Created Thu Mar 25 18:57:07 CET 2021 by tran
