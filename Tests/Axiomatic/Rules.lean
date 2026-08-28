import Tests.Axiomatic.Rules.ColourChange
import Tests.Axiomatic.Rules.EulerDecomp
import Tests.Axiomatic.Rules.HadamardHadamard
import Tests.Axiomatic.Rules.IdentityInsertion
import Tests.Axiomatic.Rules.IdentityRemoval
import Tests.Axiomatic.Rules.PiCopy
import Tests.Axiomatic.Rules.SpiderFusion
import Tests.Axiomatic.Rules.SpiderUnfusion
import Tests.Axiomatic.Rules.StrongComp

open LSpec

def rulesTests : TestSeq :=
  group "Rewrite rules" $
    colourChangeTests ++
    eulerDecompTests ++
    hadamardHadamardTests ++
    identityInsertionTests ++
    piCopyTests ++
    spiderFusionTests ++
    spiderUnfusionTests ++
    strongCompTests
