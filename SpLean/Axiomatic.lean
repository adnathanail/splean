-- The graph-style, axiomatised approach: `≈z` equivalence on `ZXDiagram`,
-- the rewrite rules it is built from, and the tactics that apply them.
import SpLean.Axiomatic.Data
import SpLean.Axiomatic.Visualize
import SpLean.Axiomatic.Axioms
import SpLean.Axiomatic.Tactics
import SpLean.Axiomatic.Rules.SpiderFusion
import SpLean.Axiomatic.Rules.IdentityRemoval
import SpLean.Axiomatic.Rules.HadamardHadamard
import SpLean.Axiomatic.Rules.ColourChange
import SpLean.Axiomatic.Rules.PiCopy
import SpLean.Axiomatic.Rules.SpiderUnfusion
import SpLean.Axiomatic.Rules.EulerDecomp
import SpLean.Axiomatic.Rules.StrongComp
import SpLean.Axiomatic.Rules.IdentityInsertion
import SpLean.Axiomatic.DerivedRules.PiPi
import SpLean.Axiomatic.Examples
