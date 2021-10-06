---- MODULE toinv_intint_t_i4 ----
EXTENDS skeen_intint_t, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_16158836067791527000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1N
const_16158836067791528000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Mcaster
\* @type: Seq(Int);
const_16158836067791529000 == 
<< 1, 2, 3 >>
----

\* CONSTANT definitions @modelParameterConstants:3MaxClock
const_16158836067791530000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:4GroupDest
\* @type: Seq(Set(Int));
const_16158836067791531000 == 
<< {1, 2}, {2, 3}, {3, 1} >> 
----

=============================================================================
\* Modification History
\* Created Tue Mar 16 09:33:26 CET 2021 by tran
