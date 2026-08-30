import SpLean.Algebraic.ZX

open SpLean.Algebraic

namespace SpLean.Algebraic.Gate

abbrev I : ZX 1 1 := .spider .Z 1 1
abbrev I_X : ZX 1 1 := .spider .X 1 1

abbrev T : ZX 1 1 := .spider .Z 1 1 (π/4)
abbrev S : ZX 1 1 := .spider .Z 1 1 (π/2)
abbrev Z : ZX 1 1 := .spider .Z 1 1 π

abbrev X : ZX 1 1 := .spider .X 1 1 π

end SpLean.Algebraic.Gate
