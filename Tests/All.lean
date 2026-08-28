import Tests.Axiomatic

open LSpec

def allTests : TestSeq :=
  group "SpLean" $
    axiomaticTests

#lspec allTests
