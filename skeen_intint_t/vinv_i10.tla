---- MODULE vinv_i10 ----
EXTENDS vinv, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_16158836067791527000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1N
const_16158836067791528000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Mcaster
\* @type: Seq(Int);
const_16158836067791529000 == 
<< 1, 2, 3, 1 >> 
----

\* CONSTANT definitions @modelParameterConstants:3MaxClock
const_16158836067791530000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:4GroupDest
\* @type: Seq(Set(Int));
const_16158836067791531000 == 
<< {1, 2, 3}, {2, 3}, {3, 1}, {1, 2} >>
----

=============================================================================
\* Modification History
\* Created Tue Mar 16 09:33:26 CET 2021 by tran
