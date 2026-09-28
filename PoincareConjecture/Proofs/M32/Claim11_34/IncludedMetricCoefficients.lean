import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients

set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M32

set_option backward.isDefEq.respectTransparency false in

theorem contDiffOn_clock_pullbackCoefficients_of_smoothFamily
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {φ : EuclideanSpace ℝ (Fin n) → M}
    (hφ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ φ V)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ)
    {K : Set ℝ} (hK : MapsTo τ K J) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (g (τ z.1)).pullbackCoefficients φ z.2) (K ×ˢ V) := by
  intro z hz
  have hf := (hφ z.2 hz.2).contMDiffAt (hV.mem_nhds hz.2)
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg hf (hK hz.1)
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  simp only [RiemannianMetric.constant_chart_bilinear_coordinates
    (n := n) (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl)] at hc
  have hid : ContMDiffWithinAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2))
      (J ×ˢ univ) (τ z.1, z.2) :=
    contDiffWithinAt_fst.contMDiffWithinAt.prodMk contDiffWithinAt_snd.contMDiffWithinAt
  have hbase : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients φ p.2)
      (J ×ˢ univ) (τ z.1, z.2) := by
    convert! (hc.comp (τ z.1, z.2) hid (fun _ hp => hp)).contDiffWithinAt using 1
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (τ p.1, p.2)) :=
    (hτ.comp contDiff_fst).prodMk contDiff_snd
  exact hbase.comp (f := fun p : ℝ × EuclideanSpace ℝ (Fin n) => (τ p.1, p.2)) z
    hmap.contDiffWithinAt
    (fun _ hp => ⟨hK hp.1, mem_univ _⟩)

end PoincareConjecture.M32
