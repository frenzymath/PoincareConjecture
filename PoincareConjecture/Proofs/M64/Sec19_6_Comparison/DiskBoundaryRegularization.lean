import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.BoundaryRegularization
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.DiskConclusion












set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture




theorem m64ExactBoundaryDisk_of_disk
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M}
    {gamma : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g gamma) :
    ∃ D' : LipschitzSpanningDisk g gamma,
      (∀ z : LoopCircle, D'.map z = gamma z) ∧ D'.area = D.area := by
  exact m60Disk_regularize_boundary g D




theorem m64DiskGluingConclusion_of_parametrized_estimates
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point}
    (A : M64Annulus (P.flow.metric t) c0 c1)
    (gamma0 gamma1 : C1FreeLoopSpace (M := M))
    (hforward : ∀ eta : ℝ, 0 < eta →
      ∀ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
        (∀ z : LoopCircle, D0.map z = gamma0 z) →
        ∃ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
          D1.area ≤ D0.area + m64ProjectedAnnulusArea P t A + eta)
    (hreverse : ∀ eta : ℝ, 0 < eta →
      ∀ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
        (∀ z : LoopCircle, D1.map z = gamma1 z) →
        ∃ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
          D0.area ≤ D1.area + m64ProjectedAnnulusArea P t A + eta) :
    M64DiskGluingConclusion P t A gamma0 gamma1 := by
  apply m64DiskGluingConclusion_of_estimates P t A gamma0 gamma1
  · intro eta heta D0
    obtain ⟨E0, hE0, harea⟩ := m64ExactBoundaryDisk_of_disk D0
    obtain ⟨D1, hD1⟩ := hforward eta heta E0 hE0
    exact ⟨D1, by simpa only [harea] using hD1⟩
  · intro eta heta D1
    obtain ⟨E1, hE1, harea⟩ := m64ExactBoundaryDisk_of_disk D1
    obtain ⟨D0, hD0⟩ := hreverse eta heta E1 hE1
    exact ⟨D0, by simpa only [harea] using hD0⟩




theorem m64DiskAreaComparison_of_parametrized_suppliers
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference) (t : ℝ)
    (hforward : ∀ (c0 c1 : ℝ → P.charts.Point)
      (A : M64Annulus (P.flow.metric t) c0 c1)
      (gamma0 gamma1 : C1FreeLoopSpace (M := M)),
      (∀ x, periodicFreeLoop gamma0 x = (c0 x).1) →
      (∀ x, periodicFreeLoop gamma1 x = (c1 x).1) →
      ∀ eta : ℝ, 0 < eta →
        ∀ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
          (∀ z : LoopCircle, D0.map z = gamma0 z) →
          ∃ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
            D1.area ≤ D0.area + m64ProjectedAnnulusArea P t A + eta)
    (hreverse : ∀ (c0 c1 : ℝ → P.charts.Point)
      (A : M64Annulus (P.flow.metric t) c0 c1)
      (gamma0 gamma1 : C1FreeLoopSpace (M := M)),
      (∀ x, periodicFreeLoop gamma0 x = (c0 x).1) →
      (∀ x, periodicFreeLoop gamma1 x = (c1 x).1) →
      ∀ eta : ℝ, 0 < eta →
        ∀ D1 : LipschitzSpanningDisk (F.metric t) gamma1,
          (∀ z : LoopCircle, D1.map z = gamma1 z) →
          ∃ D0 : LipschitzSpanningDisk (F.metric t) gamma0,
            D0.area ≤ D1.area + m64ProjectedAnnulusArea P t A + eta) :
    M64DiskAreaComparison P t := by
  intro c0 c1 A gamma0 gamma1 h0 h1
  exact m64DiskGluingConclusion_of_parametrized_estimates P t A gamma0 gamma1
    (hforward c0 c1 A gamma0 gamma1 h0 h1)
    (hreverse c0 c1 A gamma0 gamma1 h0 h1)

end PoincareConjecture
