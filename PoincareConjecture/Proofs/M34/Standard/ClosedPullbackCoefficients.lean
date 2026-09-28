import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients










set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set

namespace PoincareConjecture.RiemannianMetric

set_option backward.isDefEq.respectTransparency false in


theorem IsSmoothFamilyOn.contDiffOn_spacetime_pullbackCoefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → M} (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (J ×ˢ U) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg
    (hf.contMDiffAt (hU.mem_nhds hx)) ht
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  simp only [constant_chart_bilinear_coordinates
    (n := n) (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl)] at hc
  have hid : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2)) (t, x) :=
    contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
  have hmaps : MapsTo (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2))
      (J ×ˢ U) (J ×ˢ univ) := fun _ hp => ⟨hp.1, mem_univ _⟩
  convert! (hc.comp (t, x) hid.contMDiffWithinAt hmaps).contDiffWithinAt using 1

end PoincareConjecture.RiemannianMetric
