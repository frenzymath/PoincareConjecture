import PoincareConjecture.Statements.M64Annulus
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.DiskInfimum

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}

theorem m64DiskGluingConclusion_of_estimates
    {circumference : ℝ} (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point}
    (A : M64Annulus (P.flow.metric t) c0 c1)
    (gamma0 gamma1 : C1FreeLoopSpace (M := M))
    (hforward : ∀ eta : ℝ, 0 < eta →
      ∀ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
        ∃ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
          D1.area ≤ D0.area + m64ProjectedAnnulusArea P t A + eta)
    (hreverse : ∀ eta : ℝ, 0 < eta →
      ∀ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
        ∃ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
          D0.area ≤ D1.area + m64ProjectedAnnulusArea P t A + eta) :
    M64DiskGluingConclusion P t A gamma0 gamma1 := by
  refine
    { forward := hforward
      reverse := hreverse
      infimum := ?_ }
  intro hD0 hD1
  exact m64FillingArea_abs_sub_le_of_gluing hD0 hD1 hforward hreverse

end PoincareConjecture
