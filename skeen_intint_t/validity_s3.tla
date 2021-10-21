---- MODULE validity_s3 ----
EXTENDS validity, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_161669420062168000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1N
const_161669420062169000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2Mcaster
\* @type: Seq((Int));
const_161669420062170000 == 
<< 1, 2 >> 
----

\* CONSTANT definitions @modelParameterConstants:3MaxClock
const_161669420062171000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4GroupDest
\* @type: Seq(Set(Int));
const_161669420062172000 == 
<< {1, 2}, {1, 2} >> 
----

=============================================================================
\* Modification History
\* Created Thu Mar 25 18:43:20 CET 2021 by tran
