import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.AttainmentConclusion
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnet
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaInequality

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture

theorem m65EmbeddedFillingAreaInequality_proved
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b)) :
    M65EmbeddedFillingAreaInequality F :=
  M65Filling.embedded_filling_area_inequality_of_attainment_gaussBonnet F
    (fun q _ => m65Plateau_attainment (F.metric q) (F.connection q))
    (fun q _ => m65SuppliedDiskGaussBonnet (F.metric q) (F.connection q))

end PoincareConjecture
