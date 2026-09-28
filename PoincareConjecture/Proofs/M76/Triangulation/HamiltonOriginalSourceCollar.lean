import PoincareConjecture.Proofs.M76.Triangulation.HamiltonBoundedPuncturedImmersion
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

theorem exists_original_source_uniform_collar
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace F]
    {K : Set F} (hK : IsCompact K) {U N : Set (E × F)}
    (hU : IsOpen U) (hN : IsOpen N)
    (hsource : closedBall (0 : E) 1 ×ˢ K ⊆ U)
    (hboundary : sphere (0 : E) 1 ×ˢ K ⊆ N) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧
      ball (0 : E) b ×ˢ K ⊆ U ∧
      {x : E | a < ‖x‖ ∧ ‖x‖ < b} ×ˢ K ⊆ N ∩ U := by
  let C : Set (E × F) := closedBall (0 : E) 2 ×ˢ K
  let B : Set ℝ := (fun x : E × F => ‖x.1‖) '' (C \ (N ∩ U))
  have hC : IsCompact C := (isCompact_closedBall (0 : E) 2).prod hK
  have hB : IsCompact B :=
    (hC.diff (hN.inter hU)).image continuous_fst.norm
  have hone : (1 : ℝ) ∈ Bᶜ := by
    rintro ⟨x, hx, he⟩
    have hxone : ‖x.1‖ = 1 := he
    exact hx.2 ⟨hboundary ⟨by simpa only [mem_sphere, dist_zero_right] using hxone, hx.1.2⟩,
      hsource ⟨mem_closedBall_zero_iff.mpr hxone.le, hx.1.2⟩⟩
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl 1 hone
  let δ := min (ε / 2) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hband : {x : E | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} ×ˢ K ⊆ N ∩ U := by
    intro x hx
    by_contra hout
    have hxC : x ∈ C :=
      ⟨mem_closedBall_zero_iff.mpr (by linarith [hx.1.2]), hx.2⟩
    have hxB : ‖x.1‖ ∈ B := ⟨x, ⟨hxC, hout⟩, rfl⟩
    have hdist : ‖x.1‖ ∈ ball (1 : ℝ) ε := by
      rw [mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
    exact hεB hdist hxB
  refine ⟨1 - δ, 1 + δ, by linarith, by linarith, by linarith, ?_, hband⟩
  intro x hx
  have hxnorm : ‖x.1‖ < 1 + δ := mem_ball_zero_iff.mp hx.1
  by_cases hsmall : ‖x.1‖ ≤ 1
  · exact hsource ⟨mem_closedBall_zero_iff.mpr hsmall, hx.2⟩
  · exact (hband ⟨⟨by linarith, hxnorm⟩, hx.2⟩).2

end PoincareConjecture.M76
