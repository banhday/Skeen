---- MODULE MC_skeen_S3 ----
EXTENDS skeen, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_16158822066021301000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1N
const_16158822066021302000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2Mcaster
const_16158822066021303000 == 
<< 1, 2 >> <: Seq(Int)
----

\* CONSTANT definitions @modelParameterConstants:3MaxClock
const_16158822066021304000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4GroupDest
const_16158822066021305000 == 
<< {1}, {2} >> <: Seq({Int})
----

=============================================================================
\* Modification History
\* Created Tue Mar 16 09:10:06 CET 2021 by tran
