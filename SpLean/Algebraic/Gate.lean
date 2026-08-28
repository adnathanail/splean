import SpLean.Algebraic.ZX
import SpLean.Panel

open SpLean.Algebraic

namespace SpLean.Algebraic.Gate

abbrev T : ZX 1 1 := .spider .Z 1 1 (π/4)
abbrev S : ZX 1 1 := .spider .Z 1 1 (π/2)

abbrev X : ZX 1 1 := .spider .X 1 1 π

end SpLean.Algebraic.Gate
