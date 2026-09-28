import PoincareConjecture.Proofs.M44.Mathlib.UniformCompactDerivative
import Mathlib.Analysis.Normed.Operator.Basic











set_option autoImplicit false

open Set Filter Metric
open scoped Topology

variable {E F ι P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter ι}



theorem Filter.Tendsto.tendstoUniformlyOn_clm_apply
    {Lseq : ι → E →L[ℝ] F} {L : E →L[ℝ] F}
    (hL : Tendsto Lseq l (𝓝 L)) {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i x => Lseq i x) (fun x => L x) l K := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let B := max C 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  filter_upwards [hL.eventually (Metric.ball_mem_nhds L (div_pos hepsilon hB))] with i hi
  intro x hx
  have hn : ‖Lseq i - L‖ < epsilon / B := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hi
  have hxB : ‖x‖ ≤ B := (hC x hx).trans (le_max_left _ _)
  have hbound : ‖(Lseq i - L) x‖ < epsilon := calc
    ‖(Lseq i - L) x‖ ≤ ‖Lseq i - L‖ * ‖x‖ := (Lseq i - L).le_opNorm x
    _ ≤ ‖Lseq i - L‖ * B := mul_le_mul_of_nonneg_left hxB (norm_nonneg _)
    _ < epsilon / B * B := mul_lt_mul_of_pos_right hn hB
    _ = epsilon := div_mul_cancel₀ _ hB.ne'
  simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using hbound



theorem TendstoUniformlyOn.clm_of_apply_unitBall
    {Lseq : ι → P → E →L[ℝ] F} {L : P → E →L[ℝ] F} {K : Set P}
    (hL : TendstoUniformlyOn (fun i (z : P × E) => Lseq i z.1 z.2)
      (fun z => L z.1 z.2) l (K ×ˢ closedBall 0 1)) :
    TendstoUniformlyOn Lseq L l K := by
  rw [Metric.tendstoUniformlyOn_iff] at hL ⊢
  intro epsilon hepsilon
  filter_upwards [hL (epsilon / 2) (half_pos hepsilon)] with i hi
  intro p hp
  have hbound : ‖Lseq i p - L p‖ ≤ epsilon / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hepsilon).le
    intro v hv
    have hvB : v ∈ closedBall (0 : E) 1 := by
      simpa only [mem_closedBall, dist_zero_right, hv] using (le_refl (1 : ℝ))
    have h := (hi (p, v) ⟨hp, hvB⟩).le
    simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using h
  simpa only [dist_eq_norm, norm_sub_rev] using hbound.trans_lt (half_lt_self hepsilon)
