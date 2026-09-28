import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Coordinates
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Descent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

theorem IsSmoothFamilyOn.contDiffAt_spacetime_pullbackCoefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J) (hJ : IsOpen J)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) {t : ℝ} (ht : t ∈ J) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (t, x) := by
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg hf ht
  have hdom : J ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n))) ∈ 𝓝 (t, x) :=
    prod_mem_nhds (hJ.mem_nhds ht) Filter.univ_mem
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2.contMDiffAt hdom
  simp only [constant_chart_bilinear_coordinates
    (n := n) (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl)] at hc
  have hid : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2)) (t, x) :=
    contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
  convert! (hc.comp (t, x) hid).contDiffAt using 1

end PoincareConjecture.RiemannianMetric
