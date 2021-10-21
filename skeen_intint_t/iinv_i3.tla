---- MODULE iinv_i3 ----
EXTENDS iinv, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_16158822142051308000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1N
const_16158822142051309000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2Mcaster
\* @type: Seq(Int);
const_16158822142051310000 == 
<< 1, 2 >>
----

\* CONSTANT definitions @modelParameterConstants:3MaxClock
const_16158822142051311000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4GroupDest
\* @type: Seq(Set(Int));
const_16158822142051312000 == 
<< {1, 2}, {1, 2} >> 
----

=============================================================================
\* Modification History
\* Created Tue Mar 16 09:10:14 CET 2021 by tran
