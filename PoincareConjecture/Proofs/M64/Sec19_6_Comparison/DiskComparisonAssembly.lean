import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.DiskConclusion

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem m64DiskAreaComparison_of_suppliers
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference) (t : ℝ)
    (hforward : ∀ (c0 c1 : ℝ → P.charts.Point)
      (A : M64Annulus (P.flow.metric t) c0 c1)
      (gamma0 gamma1 : C1FreeLoopSpace (M := M)),
      (∀ x, periodicFreeLoop gamma0 x = (c0 x).1) →
      (∀ x, periodicFreeLoop gamma1 x = (c1 x).1) →
      ∀ eta : ℝ, 0 < eta →
        ∀ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
          ∃ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
            D1.area ≤ D0.area + m64ProjectedAnnulusArea P t A + eta)
    (hreverse : ∀ (c0 c1 : ℝ → P.charts.Point)
      (A : M64Annulus (P.flow.metric t) c0 c1)
      (gamma0 gamma1 : C1FreeLoopSpace (M := M)),
      (∀ x, periodicFreeLoop gamma0 x = (c0 x).1) →
      (∀ x, periodicFreeLoop gamma1 x = (c1 x).1) →
      ∀ eta : ℝ, 0 < eta →
        ∀ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
          ∃ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
            D0.area ≤ D1.area + m64ProjectedAnnulusArea P t A + eta) :
    M64DiskAreaComparison P t := by
  intro c0 c1 A gamma0 gamma1 h0 h1
  exact m64DiskGluingConclusion_of_estimates P t A gamma0 gamma1
    (hforward c0 c1 A gamma0 gamma1 h0 h1)
    (hreverse c0 c1 A gamma0 gamma1 h0 h1)

end PoincareConjecture
