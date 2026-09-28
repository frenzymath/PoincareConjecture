import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCompactImages
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedScalarConvergence
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteHarnack










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



theorem generalized_limit_terminal_scalar_le
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ} {B : ℝ}
    (G : GeneralizedBlowupConvergence S J)
    (hbound : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ S.baseBall k A, (S.flow k).scalar ⟨(S.base k).1, x⟩ ≤ B * S.scale k) :
    ∀ x, (G.limit.flow.connection 0).scalarCurvature x ≤ B := by
  intro x
  by_contra h
  have hgap : 0 < ((G.limit.flow.connection 0).scalarCurvature x - B) / 2 :=
    half_pos (sub_pos.mpr (lt_of_not_ge h))
  obtain ⟨A, hA, hcapture⟩ :=
    exists_eventually_generalized_terminal_image_baseBall G
      (isCompact_singleton (x := x))
  have herr := eventually_generalized_scalar_error G isCompact_singleton
    (singleton_subset_iff.mpr G.limit.zero_mem) (isCompact_singleton (x := x)) hgap
  obtain ⟨k, hkcap, hkerr, hkbound⟩ :=
    (hcapture.and (herr.and
      (G.subsequence_strictMono.tendsto_atTop.eventually (hbound A hA)))).exists
  have hzero := hkerr.1 (mem_singleton (0 : ℝ))
  obtain ⟨y, hy, hpoint⟩ := hkcap x (mem_singleton x)
  have herror := hkerr.2.2 0 (mem_singleton 0) hzero x (mem_singleton x)
  rw [hpoint hzero] at herror
  have hscalar := (div_le_iff₀ (S.base_scalar_pos (G.subsequence k))).mpr (hkbound y hy)
  change (S.flow (G.subsequence k)).scalar ⟨(S.base (G.subsequence k)).1, y⟩ /
    S.scale (G.subsequence k) ≤ B at hscalar
  have hlow := (abs_lt.mp herror).1
  linarith



theorem generalized_limit_terminal_scalar_le_of_short_controls
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ} {kappa r0 : ℝ}
    (H : ShortControlledBlowupHypotheses S kappa r0)
    (G : GeneralizedBlowupConvergence S J) :
    ∀ x, (G.limit.flow.connection 0).scalarCurvature x ≤ 9 * H.curvature_bound := by
  apply generalized_limit_terminal_scalar_le G
  intro A hA
  filter_upwards [H.cylinders A hA 1 zero_lt_one] with k hk
  obtain ⟨E⟩ := hk
  intro x hx
  have hzero : (0 : ℝ) ∈ Icc (-H.backward_time) 0 :=
    ⟨neg_nonpos.mpr H.backward_time_pos.le, le_rfl⟩
  have hcurv := E.curvature_bound 0 hzero x hx
  rw [E.zero_identity hzero x hx] at hcurv
  have hscalar := (le_abs_self _).trans
    (((S.flow k).connection (S.base k).1).abs_scalarCurvature_le_curvatureTensorNorm x)
  have hnorm : ((S.flow k).connection (S.base k).1).curvatureTensorNorm x ≤
      H.curvature_bound * S.scale k := (le_abs_self _).trans hcurv
  norm_num only [Nat.cast_ofNat, sq] at hscalar
  exact hscalar.trans (by nlinarith [S.base_scalar_pos k])



theorem finite_limit_scalar_le_of_terminal_bound
    (hC : RicciFlowCurvatureTheory.{u}) (hH : HarnackAncientTheory.{u})
    {T B : ℝ} (L : BlowupLimitFlow.{u} (Ioc (-T) 0))
    (hterminal : ∀ x, (L.flow.connection 0).scalarCurvature x ≤ B) :
    ∀ t ∈ Ioc (-T) 0, ∀ x,
      (L.flow.connection t).scalarCurvature x ≤ B * T / (t + T) := by
  have hT : 0 < T := by linarith [L.zero_mem.1]
  have hbounded (t : ℝ) (ht : t ∈ Ioc (-T) 0) :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x, (L.flow.connection t).curvatureTensorNorm x ≤ K := by
    obtain ⟨K, hK, hnorm⟩ := L.curvature_locally_bounded_in_time {t}
      isCompact_singleton (singleton_subset_iff.mpr ht)
    exact ⟨K, hK, fun x => (le_abs_self _).trans (hnorm t (mem_singleton t) x)⟩
  intro t ht x
  have hmono := monotoneOn_weighted_scalar_on_Ioc hC hH
    (show -T < 0 by linarith) L.flow L.complete
    L.nonnegative_curvature_operator hbounded x ht L.zero_mem ht.2
  have hweight := mul_le_mul_of_nonneg_left (hterminal x) hT.le
  apply (le_div_iff₀ (show 0 < t + T by linarith [ht.1])).mpr
  simp only [sub_neg_eq_add, zero_add] at hmono
  nlinarith

end PoincareConjecture.M30
