---- MODULE integrity_s3 ----
EXTENDS integrity, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_161669420062168000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1N
const_161669420062169000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2Mcaster
const_161669420062170000 == 
<< 1, 2 >> <: Seq(Int)
----

\* CONSTANT definitions @modelParameterConstants:3MaxClock
const_161669420062171000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4GroupDest
const_161669420062172000 == 
<< {1, 2}, {1, 2} >> <: Seq({Int})
----

=============================================================================
\* Modification History
\* Created Thu Mar 25 18:43:20 CET 2021 by tran
