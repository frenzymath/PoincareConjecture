import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularLengthMap
import PoincareConjecture.Proofs.M60.Mathlib.CompactExtendedLipschitz

set_option autoImplicit false

open Set Filter Metric
open scoped Topology NNReal ENNReal

namespace PoincareConjecture

theorem m60AnnularLengthMap_lipschitz
    {E : Type*} [PseudoEMetricSpace E] {beta : ℝ → E} {a b : ℝ → ℝ}
    {A B C : ℝ≥0} (ha : LipschitzWith A a) (hb : LipschitzWith B b)
    {S : Set ℝ} (hS : Convex ℝ S) (haS : ∀ t, a t ∈ S) (hbS : ∀ t, b t ∈ S)
    (hbeta : LipschitzOnWith C beta S)
    (hp : ∀ u ∈ Icc (0 : ℝ) 1, Function.Periodic
      (fun t => beta (M60.lengthParameterInterpolation a b (u, t))) rampPeriod) :
    ∃ K : ℝ≥0, LipschitzOnWith K (m60AnnularLengthMap beta a b)
      {z : LoopPlane | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
  let Q := {z : LoopPlane | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1}
  have hQ : IsCompact Q := by
    have heq : Q = closedBall (0 : LoopPlane) 1 ∩ {z : LoopPlane | 1 / 2 ≤ ‖z‖} := by
      ext z
      simp only [Q, mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact and_comm
    rw [heq]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hmem (theta : LoopPlane → ℝ) (z : LoopPlane) (hz : z ∈ Q) :
      M60.lengthParameterInterpolation a b (2 * ‖z‖ - 1, theta z) ∈ S :=
    M60.lengthParameterInterpolation_mem hS haS hbS ⟨by linarith [hz.1], by linarith [hz.2]⟩
  apply M60.exists_lipschitzOnWith_of_compact_edist_ne_top hQ
  · intro z hz
    have hn : z ≠ 0 := by
      intro heq
      have h := hz.1
      rw [heq, norm_zero] at h
      norm_num at h
    obtain ⟨theta, K, U, hU, hLip, heq⟩ := m60AnnularLengthMap_local_scalar ha hb hp hn
    refine ⟨C * K, U ∩ Q, inter_mem (nhdsWithin_le_nhds hU) self_mem_nhdsWithin, ?_⟩
    intro x hx y hy
    rw [heq x hx.2, heq y hy.2]
    exact (hbeta.comp (hLip.mono inter_subset_left)
      (fun w hw => hmem theta w hw.2)) hx hy
  · intro x hx y hy
    have h := hbeta (hmem m60PlaneAngle x hx) (hmem m60PlaneAngle y hy)
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) h

end PoincareConjecture
