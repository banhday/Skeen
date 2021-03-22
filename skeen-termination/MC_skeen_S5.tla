---- MODULE MC_skeen_S5 ----
EXTENDS skeen, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_16158836067791527000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1N
const_16158836067791528000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Mcaster
const_16158836067791529000 == 
<< 1, 2, 3 >> <: Seq(Int)
----

\* CONSTANT definitions @modelParameterConstants:3MaxClock
const_16158836067791530000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:4GroupDest
const_16158836067791531000 == 
<< {1, 2}, {2, 3}, {3, 1} >> <: Seq({Int})
----

=============================================================================
\* Modification History
\* Created Tue Mar 16 09:33:26 CET 2021 by tran
