import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Topology.OpenPartialHomeomorph.Constructions









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem limitFinite_exists_chart_buffer
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ConnectedSpace M] (g : RiemannianMetric 3 M) (y o z : M)
    (hyo : y ≠ o) (hyz : y ≠ z) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (r eta : ℝ),
      0 < r ∧ 0 < eta ∧
      closedBall (0 : EuclideanSpace ℝ (Fin 3)) r ⊆ c.target ∧
      o ∉ c.symm '' ball 0 r ∧ z ∉ c.symm '' ball 0 r ∧
      g.ball y eta ⊆ c.source ∩ c ⁻¹' ball 0 r := by
  let := g.toMetricSpace
  let c := (chartAt (EuclideanSpace ℝ (Fin 3)) y).transHomeomorph
    (Homeomorph.addRight (-(chartAt (EuclideanSpace ℝ (Fin 3)) y) y))
  have hyc : y ∈ c.source := mem_chart_source _ y
  have hcy : c y = 0 := by simp [c]
  have hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ c.target := hcy ▸ c.map_source hyc
  have hinverse : c.symm 0 = y := by simpa only [hcy] using c.left_inv hyc
  let V : Set M := {o}ᶜ ∩ {z}ᶜ
  have hV : IsOpen V := isClosed_singleton.isOpen_compl.inter
    isClosed_singleton.isOpen_compl
  have hyV : y ∈ V := ⟨hyo, hyz⟩
  have hU : IsOpen (c.target ∩ c.symm ⁻¹' V) :=
    c.symm.continuousOn.isOpen_inter_preimage c.open_target hV
  have hzeroU : (0 : EuclideanSpace ℝ (Fin 3)) ∈ c.target ∩ c.symm ⁻¹' V :=
    ⟨hzero, by simpa only [mem_preimage, hinverse] using hyV⟩
  obtain ⟨r, hr, hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hU.mem_nhds hzeroU)
  have hsmallOpen : IsOpen (c.source ∩ c ⁻¹' ball 0 r) :=
    c.continuousOn.isOpen_inter_preimage c.open_source isOpen_ball
  have hsmallY : y ∈ c.source ∩ c ⁻¹' ball 0 r :=
    ⟨hyc, by simpa only [mem_preimage, hcy, mem_ball, dist_self] using hr⟩
  obtain ⟨eta, heta, hmetric⟩ := Metric.mem_nhds_iff.mp (hsmallOpen.mem_nhds hsmallY)
  refine ⟨c, r, eta, hr, heta, fun x hx => (hclosed hx).1, ?_, ?_, ?_⟩
  · rintro ⟨x, hx, hxo⟩
    exact (hclosed (ball_subset_closedBall hx)).2.1 hxo
  · rintro ⟨x, hx, hxz⟩
    exact (hclosed (ball_subset_closedBall hx)).2.2 hxz
  · simpa only [g.toMetricSpace_ball y eta] using hmetric

end PoincareConjecture.M47
