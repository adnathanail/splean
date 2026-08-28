import Tests.Axiomatic
import Tests.Algebraic

open LSpec

def main (args : List String) : IO UInt32 :=
  lspecIO (.ofList [("SpLean", [Tests.Axiomatic.tests, Tests.Algebraic.tests])]) args
