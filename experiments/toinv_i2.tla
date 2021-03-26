---- MODULE toinv_i2 ----
EXTENDS toinv, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_16158821936111287000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1N
const_16158821936111288000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2Mcaster
const_16158821936111289000 == 
<< 1, 1 >> <: Seq(Int)
----

\* CONSTANT definitions @modelParameterConstants:3MaxClock
const_16158821936111290000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4GroupDest
const_16158821936111291000 == 
<< {1}, {1} >> <: Seq({Int})
----

=============================================================================
\* Modification History
\* Created Tue Mar 16 09:09:53 CET 2021 by tran
