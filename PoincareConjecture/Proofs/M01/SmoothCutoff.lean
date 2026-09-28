import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus



set_option autoImplicit false

open Manifold Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem m01_exists_smooth_cutoff (x : M) (U : Set M)
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ y, 0 ≤ f y) ∧ 0 < f x ∧ tsupport f ⊆ U := by
  classical
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hxs : x ∈ e.source := mem_chart_source _ x
  have hxt : e x ∈ e.target := e.map_source hxs
  have hN : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (e x) :=
    inter_mem (e.open_target.mem_nhds hxt)
      ((e.continuousAt_symm hxt).preimage_mem_nhds
        (hU.mem_nhds (by simpa only [e.left_inv hxs] using hx)))
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hN
  let b : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => expNegInvGlue (R ^ 2 - ‖z - e x‖ ^ 2)
  have hb : ContDiff ℝ ∞ b :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))
  let f : M → ℝ := e.source.indicator (fun y => b (e y))
  let K : Set M := e.symm '' Metric.closedBall (e x) R
  have hKclosed : IsClosed K :=
    ((isCompact_closedBall (e x) R).image_of_continuousOn
      (e.continuousOn_symm.mono (fun z hz => (hball hz).1))).isClosed
  have hKsource : K ⊆ e.source := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_target (hball hz).1
  have hKU : K ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact (hball hz).2
  have hsupp : Function.support f ⊆ K := by
    intro y hy
    have hys : y ∈ e.source := by
      by_contra h
      exact hy (by simp [f, h])
    have hnonzero : b (e y) ≠ 0 := by simpa [f, hys] using hy
    have hnorm : ‖e y - e x‖ ≤ R := by
      have hpos : 0 < R ^ 2 - ‖e y - e x‖ ^ 2 := by
        exact lt_of_not_ge (fun h => hnonzero (expNegInvGlue.zero_of_nonpos h))
      nlinarith [norm_nonneg (e y - e x)]
    exact ⟨e y, by simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm,
      e.left_inv hys⟩
  have htsupp : tsupport f ⊆ K := closure_minimal hsupp hKclosed
  refine ⟨f, ?_, ?_, ?_, htsupp.trans hKU⟩
  · apply contMDiff_of_tsupport
    intro y hy
    have hys := hKsource (htsupp hy)
    have he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e y :=
      contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hys)
    apply (hb.contMDiff.contMDiffAt.comp y he).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hys] with z hz
    simp [f, hz]
  · intro y
    by_cases hy : y ∈ e.source
    · simpa [f, hy, b] using expNegInvGlue.nonneg (R ^ 2 - ‖e y - e x‖ ^ 2)
    · simp [f, hy]
  · simpa [f, hxs, b] using expNegInvGlue.pos_of_pos (sq_pos_of_pos hR)

end PoincareConjecture
