import Tests.Axiomatic.Rules.ColourChange
import Tests.Axiomatic.Rules.EulerDecomp
import Tests.Axiomatic.Rules.HadamardHadamard
import Tests.Axiomatic.Rules.IdentityInsertion
import Tests.Axiomatic.Rules.IdentityRemoval
import Tests.Axiomatic.Rules.PiCopy
import Tests.Axiomatic.Rules.SpiderFusion
import Tests.Axiomatic.Rules.SpiderUnfusion
import Tests.Axiomatic.Rules.StrongComp

namespace Tests.Axiomatic.Rules

open LSpec

def tests : TestSeq :=
  group "Rewrite rules" $
    ColourChange.tests ++
    EulerDecomp.tests ++
    HadamardHadamard.tests ++
    IdentityInsertion.tests ++
    IdentityRemoval.tests ++
    PiCopy.tests ++
    SpiderFusion.tests ++
    SpiderUnfusion.tests ++
    StrongComp.tests

end Tests.Axiomatic.Rules
