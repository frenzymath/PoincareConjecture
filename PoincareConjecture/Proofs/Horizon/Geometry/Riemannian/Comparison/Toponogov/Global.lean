import PoincareConjecture.Proofs.Horizon.Analysis.Convex.UpperSupport
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture.RiemannianMetric

theorem squared_distance_defect_concave_of_second_deriv_nonpos
    {F : ℝ → ℝ} {b : ℝ}
    (hF : DifferentiableOn ℝ (fun t => F t - t ^ 2) (Icc 0 b))
    (hF' : DifferentiableOn ℝ (deriv (fun t => F t - t ^ 2)) (Icc 0 b))
    (hF'' : ∀ t ∈ Icc 0 b,
      deriv^[2] (fun s => F s - s ^ 2) t ≤ 0) :
    ConcaveOn ℝ (Icc 0 b) (fun t => F t - t ^ 2) := by
  exact concaveOn_of_deriv2_nonpos' (convex_Icc 0 b) hF hF' hF''

theorem squared_distance_defect_concave_of_upper_supports
    {F : ℝ → ℝ} {b : ℝ} (hF : ContinuousOn F (Icc 0 b))
    (hsupport : ∀ t ∈ Ioo 0 b, ∀ ε : ℝ, 0 < ε →
      ∃ u : ℝ → ℝ, ContDiffAt ℝ 2 u t ∧ u t = F t ∧
        (∀ᶠ s in 𝓝 t, F s ≤ u s) ∧ deriv (deriv u) t ≤ 2 + ε) :
    ConcaveOn ℝ (Icc 0 b) (fun t => F t - t ^ 2) := by
  simpa only [one_mul] using
    Poincare.Analysis.concaveOn_sub_quadratic_of_approximate_upper_support
      (C := 1) hF (by simpa only [mul_one] using hsupport)

theorem hinge_upper_of_squared_distance_upper_supports
    {F u : ℝ → ℝ} {a b q : ℝ} (hb : 0 < b)
    (hzero : F 0 = a ^ 2) (hF : ContinuousOn F (Icc 0 b))
    (htouch : u 0 = F 0) (hupper : ∀ᶠ s in 𝓝 0, F s ≤ u s)
    (hu : HasDerivAt u (-2 * a * q) 0)
    (hsupport : ∀ t ∈ Ioo 0 b, ∀ ε : ℝ, 0 < ε →
      ∃ v : ℝ → ℝ, ContDiffAt ℝ 2 v t ∧ v t = F t ∧
        (∀ᶠ s in 𝓝 t, F s ≤ v s) ∧ deriv (deriv v) t ≤ 2 + ε) :
    F b ≤ a ^ 2 + b ^ 2 - 2 * a * b * q := by
  have hd : HasDerivAt (fun s => u s - s ^ 2) (-2 * a * q) 0 := by
    convert! hu.sub ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
    simp
  have h := Poincare.Analysis.le_affine_of_concaveOn_of_upper_support hb
    (squared_distance_defect_concave_of_upper_supports hF hsupport)
    (show u 0 - (0 : ℝ) ^ 2 = F 0 - (0 : ℝ) ^ 2 by rw [htouch])
    (hupper.mono fun s hs => sub_le_sub_right hs (s ^ 2)) hd
  simp only [hzero, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at h
  nlinarith

theorem hinge_upper_of_squared_distance_semiconcavity
    {F : ℝ → ℝ} {a b q : ℝ}
    (_ha : 0 < a) (hb : 0 < b)
    (hzero : F 0 = a ^ 2)
    (hderiv : HasDerivAt (fun t => F t - t ^ 2) (-2 * a * q) 0)
    (hconc : ConcaveOn ℝ (Icc 0 b) (fun t => F t - t ^ 2)) :
    F b ≤ a ^ 2 + b ^ 2 - 2 * a * b * q := by
  have hsl := hconc.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 b by exact ⟨le_rfl, hb.le⟩)
    (show b ∈ Icc 0 b by exact ⟨hb.le, le_rfl⟩) hb
    hderiv
  rw [slope_def_field, sub_zero, hzero] at hsl
  field_simp [ne_of_gt hb] at hsl
  linarith

theorem hinge_upper_of_squared_distance_second_deriv_nonpos
    {F : ℝ → ℝ} {a b q : ℝ}
    (_ha : 0 < a) (hb : 0 < b)
    (hzero : F 0 = a ^ 2)
    (hderiv : HasDerivAt (fun t => F t - t ^ 2) (-2 * a * q) 0)
    (hF : DifferentiableOn ℝ (fun t => F t - t ^ 2) (Icc 0 b))
    (hF' : DifferentiableOn ℝ (deriv (fun t => F t - t ^ 2)) (Icc 0 b))
    (hF'' : ∀ t ∈ Icc 0 b,
      deriv^[2] (fun s => F s - s ^ 2) t ≤ 0) :
    F b ≤ a ^ 2 + b ^ 2 - 2 * a * b * q := by
  exact hinge_upper_of_squared_distance_semiconcavity _ha hb hzero hderiv
    (squared_distance_defect_concave_of_second_deriv_nonpos hF hF' hF'')

theorem corresponding_side_lower_of_squared_distance_semiconcavity
    {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (haxis₁ : ∀ t ∈ Icc 0 b,
      ConcaveOn ℝ (Icc 0 a) (fun s => F s t - s ^ 2))
    (haxis₂ : ∀ s ∈ Icc 0 a,
      ConcaveOn ℝ (Icc 0 b) (fun t => F s t - t ^ 2))
    (hzero₁ : ∀ s ∈ Icc 0 a, F s 0 = s ^ 2)
    (hzero₂ : ∀ t ∈ Icc 0 b, F 0 t = t ^ 2) :
    ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 b,
      F s t ≥ s ^ 2 + t ^ 2 -
        2 * s * t * ((a ^ 2 + b ^ 2 - F a b) / (2 * a * b)) := by
  exact Poincare.Analysis.two_parameter_chord_lower_bound ha hb haxis₁ haxis₂
    hzero₁ hzero₂

theorem corresponding_side_lower_of_squared_distance_second_deriv_nonpos
    {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (haxis₁ : ∀ t ∈ Icc 0 b,
      DifferentiableOn ℝ (fun s => F s t - s ^ 2) (Icc 0 a))
    (haxis₁' : ∀ t ∈ Icc 0 b,
      DifferentiableOn ℝ (deriv (fun s => F s t - s ^ 2)) (Icc 0 a))
    (haxis₁'' : ∀ t ∈ Icc 0 b, ∀ s ∈ Icc 0 a,
      deriv^[2] (fun u => F u t - u ^ 2) s ≤ 0)
    (haxis₂ : ∀ s ∈ Icc 0 a,
      DifferentiableOn ℝ (fun t => F s t - t ^ 2) (Icc 0 b))
    (haxis₂' : ∀ s ∈ Icc 0 a,
      DifferentiableOn ℝ (deriv (fun t => F s t - t ^ 2)) (Icc 0 b))
    (haxis₂'' : ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 b,
      deriv^[2] (fun u => F s u - u ^ 2) t ≤ 0)
    (hzero₁ : ∀ s ∈ Icc 0 a, F s 0 = s ^ 2)
    (hzero₂ : ∀ t ∈ Icc 0 b, F 0 t = t ^ 2) :
    ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 b,
      F s t ≥ s ^ 2 + t ^ 2 -
        2 * s * t * ((a ^ 2 + b ^ 2 - F a b) / (2 * a * b)) := by
  apply corresponding_side_lower_of_squared_distance_semiconcavity ha hb
  · intro t ht
    exact squared_distance_defect_concave_of_second_deriv_nonpos
      (haxis₁ t ht) (haxis₁' t ht) (haxis₁'' t ht)
  · intro s hs
    exact squared_distance_defect_concave_of_second_deriv_nonpos
      (haxis₂ s hs) (haxis₂' s hs) (haxis₂'' s hs)
  · exact hzero₁
  · exact hzero₂

end PoincareConjecture.RiemannianMetric
