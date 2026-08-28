import Tests.Axiomatic

open LSpec

def main (args : List String) : IO UInt32 :=
  lspecIO (.ofList [("SpLean", [Tests.Axiomatic.tests])]) args
