import PoincareConjecture.Definitions.Ch01.RiemannianMetric









set_option autoImplicit false

open scoped ContDiff Topology
open Set

namespace PoincareConjecture.Proofs.M03

theorem exists_smooth_coordinate_cutoff
    {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧
      EqOn φ (fun _ => 1) (Metric.closedBall c r) ∧
      tsupport φ ⊆ Metric.closedBall c R := by
  have hR : 0 < R := hr.trans hrR
  have hd : 0 < R ^ 2 - r ^ 2 :=
    sub_pos.mpr ((sq_lt_sq₀ hr.le hR.le).mpr hrR)
  let φ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => Real.smoothTransition ((R ^ 2 - ‖x - c‖ ^ 2) / (R ^ 2 - r ^ 2))
  have hφ : ContDiff ℝ ∞ φ :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const _)
  have hsupp : tsupport φ ⊆ Metric.closedBall c R := by
    apply closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    by_contra hball
    have hnorm : R < ‖x - c‖ := by
      change ¬ dist x c ≤ R at hball
      rw [dist_eq_norm] at hball
      exact lt_of_not_ge hball
    apply hx
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ((sq_le_sq₀ hR.le (norm_nonneg _)).mpr hnorm.le)) hd.le
  refine ⟨φ, hφ, (isCompact_closedBall c R).of_isClosed_subset
    (isClosed_tsupport φ) hsupp, ?_, ?_, hsupp⟩
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hd).mpr
    have hnorm : ‖x - c‖ ≤ r := by
      change dist x c ≤ r at hx
      rw [dist_eq_norm] at hx
      exact hx
    have hsq := (sq_le_sq₀ (norm_nonneg (x - c)) hr.le).mpr hnorm
    linarith

end PoincareConjecture.Proofs.M03
