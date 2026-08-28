import Tests.Axiomatic.Normalization
import Tests.Axiomatic.Rules

open LSpec

def axiomaticTests : TestSeq :=
  group "Axiomatic" $
    normalizationTests ++
    rulesTests

#lspec axiomaticTests
