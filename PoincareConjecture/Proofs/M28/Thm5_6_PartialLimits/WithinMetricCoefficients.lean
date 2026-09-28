import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

theorem IsSmoothFamilyOn.contDiffOn_spacetime_pullbackCoefficients_within
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J)
    {f : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (J ×ˢ U) := by
  intro p hp
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg
    ((hf p.2 hp.2).contMDiffAt (hU.mem_nhds hp.2)) hp.1
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  simp only [constant_chart_bilinear_coordinates
    (n := n) (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl)] at hc
  have hid : ContMDiffWithinAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (z.1, z.2)) (J ×ˢ U) p :=
    contDiffWithinAt_fst.contMDiffWithinAt.prodMk contDiffWithinAt_snd.contMDiffWithinAt
  convert (hc.comp p hid
    (show MapsTo (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (z.1, z.2))
      (J ×ˢ U) (J ×ˢ univ) from fun z hz => ⟨hz.1, mem_univ _⟩)).contDiffWithinAt using 1
  rfl

end PoincareConjecture.RiemannianMetric
