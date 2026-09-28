import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedComparison
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.Conclusion








set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture





theorem m65ImmersedFillingAreaComparison_proved
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (V : M64ThreeDimensionalFlowConclusion F) :
    M65ImmersedFillingAreaComparison F :=
  m65ImmersedFillingAreaComparison_of_embedded F V
    (m65EmbeddedFillingAreaInequality_proved F)

end PoincareConjecture
