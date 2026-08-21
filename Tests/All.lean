import Tests.SpiderFusion
import Tests.SpiderUnfusion
import Tests.IdentityRemoval
import Tests.PiCopy
import Tests.HadamardHadamard
import Tests.EulerDecomp
import Tests.ColourChange
import Tests.Normalization
import Tests.StrongComp
import Tests.IdentityInsertion

open LSpec

#lspec spiderFusionTests ++ spiderUnfusionTests ++ identityRemovalTests ++ identityInsertionTests ++ piCopyTests ++ hadamardHadamardTests ++ colourChangeTests ++ eulerDecompTests ++ normalizationTests ++ strongCompTests
