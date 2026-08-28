import Tests.Axiomatic.Normalization
import Tests.Axiomatic.Rules

namespace Tests.Axiomatic

open LSpec

def tests : TestSeq :=
  group "Axiomatic" $
    Normalization.tests ++
    Rules.tests

end Tests.Axiomatic
