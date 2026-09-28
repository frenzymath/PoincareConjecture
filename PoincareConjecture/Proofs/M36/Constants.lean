import PoincareConjecture.Proofs.M36.ProfileBounds

set_option autoImplicit false

namespace PoincareConjecture.M36

noncomputable def profileConstants (g₀ : StandardInitialMetric)
    (q C R upper : ℝ) (comparison : ℝ → ℝ)
    (hq : 100 < q) (hC : 100 * q < C) (hR : 0 < R) (hupper : 0 < upper)
    (hcomparison : ∀ eta : ℝ, 0 < eta → 0 < comparison eta) :
    MetricSurgeryConstants where
  C₀ := C
  q := q
  R₀ := R
  delta₀ := (exists_neck_threshold g₀ hupper).choose
  C₀_pos := by linarith
  C₀_gt_one := by linarith
  q_pos := by linarith
  q_gt_one := by linarith
  R₀_pos := hR
  delta₀_pos := (exists_neck_threshold g₀ hupper).choose_spec.1
  delta₀_lt := (exists_neck_threshold g₀ hupper).choose_spec.2.1
  comparison_delta := comparison
  comparison_delta_pos := hcomparison

theorem profileConstants_largeQ (g₀ : StandardInitialMetric)
    (q C R upper : ℝ) (comparison : ℝ → ℝ)
    (hq : 100 < q) (hC : 100 * q < C) (hR : 0 < R) (hupper : 0 < upper)
    (hcomparison : ∀ eta : ℝ, 0 < eta → 0 < comparison eta)
    (hA : 100 * (4 + g₀.cylindrical_end.radius) ^ 2 < q) :
    SurgeryProfileLargeQ g₀
      (profileConstants g₀ q C R upper comparison hq hC hR hupper hcomparison) :=
  largeQ_of_bounds g₀ _ hq hA

theorem profileConstants_dominance (g₀ : StandardInitialMetric)
    (q C R upper : ℝ) (comparison : ℝ → ℝ)
    (hq : 100 < q) (hC : 100 * q < C) (hR : 0 < R) (hupper : 0 < upper)
    (hcomparison : ∀ eta : ℝ, 0 < eta → 0 < comparison eta) :
    let K := profileConstants g₀ q C R upper comparison hq hC hR hupper hcomparison
    100 * K.q < K.C₀ := hC

theorem profileConstants_delta_le (g₀ : StandardInitialMetric)
    (q C R upper : ℝ) (comparison : ℝ → ℝ)
    (hq : 100 < q) (hC : 100 * q < C) (hR : 0 < R) (hupper : 0 < upper)
    (hcomparison : ∀ eta : ℝ, 0 < eta → 0 < comparison eta) :
    (profileConstants g₀ q C R upper comparison hq hC hR hupper hcomparison).delta₀ ≤
      upper :=
  (exists_neck_threshold g₀ hupper).choose_spec.2.2.1

theorem profileConstants_cutoff_inside (g₀ : StandardInitialMetric)
    (q C R upper : ℝ) (comparison : ℝ → ℝ)
    (hq : 100 < q) (hC : 100 * q < C) (hR : 0 < R) (hupper : 0 < upper)
    (hcomparison : ∀ eta : ℝ, 0 < eta → 0 < comparison eta)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hle : epsilon ≤
      (profileConstants g₀ q C R upper comparison hq hC hR hupper hcomparison).delta₀) :
    4 + g₀.cylindrical_end.radius < epsilon⁻¹ :=
  (exists_neck_threshold g₀ hupper).choose_spec.2.2.2 epsilon hepsilon hle

end PoincareConjecture.M36
