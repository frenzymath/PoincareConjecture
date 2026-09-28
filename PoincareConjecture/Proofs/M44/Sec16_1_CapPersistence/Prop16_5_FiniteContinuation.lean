import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_InitialStage
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_RestartStage










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M44





theorem exists_cap_sequence_full_stage
    (P : M44CapPersistencePredecessors.{u})
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    {rNext Rinner theta : ℝ} (hr : 0 < rNext) (hinner : 0 < Rinner)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    {start A eta : ℝ} {cutoffs : ℕ → ℝ}
    (X : ∀ n, PreparedCapCounterexample.{u}
      setup start rNext A eta theta (cutoffs n) Rinner)
    (hcutoffs : Tendsto cutoffs atTop (𝓝 0))
    (heta : Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0))
    {c : ℝ} (hc : 0 ≤ c) (hctheta : c ≤ theta)
    (hlim : Tendsto (fun n => (X n).sample.lifetime) atTop (𝓝 c)) :
    ∃ R0 K : ℝ, Rinner < R0 ∧ 0 < K ∧
      ∃ T : ℝ, 0 < T ∧ c < T ∧ CapSequenceStage X R0 T K := by
  obtain ⟨Rinitial, Tinitial, Ki, hinnerInitial, _hRinitial, hTinitial, hKi, hinitial⟩ :=
    exists_initial_cap_sequence_stage P setup standard hr hinner
  obtain ⟨Rrestart, increment, K, _hinnerRestart, _hRrestart, hincrement, hK, hKiK,
    hrestart⟩ := exists_cap_sequence_restart P setup standard unique hr hinner
      htheta htheta1 hKi
  let R0 := max Rinitial Rrestart
  have hInitial : CapSequenceStage X R0 Tinitial K :=
    (hinitial start A eta theta X hcutoffs heta).mono (le_max_left _ _) le_rfl hKiK
  have hstep (T : ℝ) (hT : 0 < T) (hTc : T ≤ c)
      (hstage : CapSequenceStage X R0 T K) :
      CapSequenceStage X R0 (T + increment) K :=
    hrestart start A eta X hcutoffs heta c hc hctheta hlim R0 T
      (le_max_right _ _) hT hTc hstage
  refine ⟨R0, K, hinnerInitial.trans_le (le_max_left _ _), hK, ?_⟩
  by_contra! hnot
  have hupper (T : ℝ) (hT : 0 < T) (hstage : CapSequenceStage X R0 T K) : T ≤ c := by
    by_contra hgt
    exact hnot T hT (lt_of_not_ge hgt) hstage
  have hlevels (n : ℕ) : CapSequenceStage X R0 (Tinitial + (n : ℝ) * increment) K := by
    induction n with
    | zero => simpa using hInitial
    | succ n hn =>
      have hpositive : 0 < Tinitial + (n : ℝ) * increment :=
        add_pos_of_pos_of_nonneg hTinitial (mul_nonneg (Nat.cast_nonneg n) hincrement.le)
      have hnext := hstep _ hpositive (hupper _ hpositive hn) hn
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using hnext
  obtain ⟨n, hn⟩ := exists_nat_gt ((c - Tinitial) / increment)
  have hgreater : c < Tinitial + (n : ℝ) * increment := by
    have hmul := (div_lt_iff₀ hincrement).mp hn
    linarith
  have hpositive : 0 < Tinitial + (n : ℝ) * increment :=
    add_pos_of_pos_of_nonneg hTinitial (mul_nonneg (Nat.cast_nonneg n) hincrement.le)
  exact hnot _ hpositive hgreater (hlevels n)

end PoincareConjecture.M44
