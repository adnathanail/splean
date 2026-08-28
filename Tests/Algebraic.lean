import Tests.Algebraic.AlgPhase

namespace Tests.Algebraic

open LSpec

def tests : TestSeq :=
  group "Algebraic" $
    AlgPhase.tests

end Tests.Algebraic
