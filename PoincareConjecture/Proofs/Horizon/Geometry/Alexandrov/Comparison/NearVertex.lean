import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.ComparisonAngle
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace Poincare.Alexandrov

theorem cos_comparisonAngle_change_vertex {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hlow : |a - b| ≤ c) (hhigh : c ≤ a + b) :
    Real.cos (comparisonAngle a c b) =
      (Real.sinh a * Real.cosh b - Real.cosh a * Real.sinh b *
        Real.cos (comparisonAngle a b c)) / Real.sinh c := by
  have hlow' : |a - c| ≤ b := abs_le.mpr ⟨by linarith, by
    have h := le_abs_self (a - b)
    linarith⟩
  have hhigh' : b ≤ a + c := by
    have h := neg_le_abs (a - b)
    linarith
  rw [cos_comparisonAngle ha hc hb.le hlow' hhigh',
    cos_comparisonAngle ha hb hc.le hlow hhigh]
  have hsa := (Real.sinh_pos_iff.mpr ha).ne'
  have hsb := (Real.sinh_pos_iff.mpr hb).ne'
  have hsc := (Real.sinh_pos_iff.mpr hc).ne'
  field_simp
  linear_combination (Real.cosh b) * (Real.cosh_sq_sub_sinh_sq a)

theorem exists_pos_comparisonAngle_near_vertex {b α : ℝ}
    (hb : 0 < b) (hα : 0 < α) (hαpi : α < Real.pi / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a c : ℝ, 0 < a → a < ε →
      |a - b| ≤ c → c ≤ a + b → comparisonAngle a b c ≤ α →
      Real.pi - 2 * α < comparisonAngle a c b := by
  let F : ℝ × ℝ → ℝ := fun v =>
    (Real.sinh v.1 * Real.cosh b - Real.cosh v.1 * Real.sinh b * Real.cos α) /
      Real.sinh v.2
  have hF : ContinuousAt F (0, b) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact (Real.sinh_pos_iff.mpr hb).ne'
  have hFzero : F (0, b) = -Real.cos α := by
    dsimp [F]
    simp only [Real.sinh_zero, Real.cosh_zero, zero_mul, one_mul, zero_sub]
    field_simp
  have hcos : Real.cos (2 * α) < Real.cos α :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hα.le (by linarith) (by linarith)
  have hgap : F (0, b) < Real.cos (Real.pi - 2 * α) := by
    rw [hFzero, Real.cos_pi_sub]
    linarith
  have hev : ∀ᶠ v in 𝓝 (0, b), F v < Real.cos (Real.pi - 2 * α) :=
    hF.eventually_lt continuousAt_const hgap
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min r (b / 2), lt_min hr (by positivity), ?_⟩
  intro a c ha har hlow hhigh hangle
  have har' : a < r := har.trans_le (min_le_left _ _)
  have hab : a < b / 2 := har.trans_le (min_le_right _ _)
  have hcb : |c - b| ≤ a := abs_le.mpr ⟨by
    have h := neg_le_abs (a - b)
    linarith, by linarith⟩
  have hc : 0 < c := by
    have h := neg_le_abs (a - b)
    linarith
  have hFbound : F (a, c) < Real.cos (Real.pi - 2 * α) := by
    apply hball
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero, abs_of_pos ha]
    exact max_lt har' (hcb.trans_lt har')
  have hcosangle : Real.cos α ≤ Real.cos (comparisonAngle a b c) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (comparisonAngle_nonneg a b c)
      (by linarith [Real.pi_pos]) hangle
  have hupper : Real.cos (comparisonAngle a c b) ≤ F (a, c) := by
    rw [cos_comparisonAngle_change_vertex ha hb hc hlow hhigh]
    apply div_le_div_of_nonneg_right _ (Real.sinh_pos_iff.mpr hc).le
    have hmul := mul_le_mul_of_nonneg_left hcosangle
      (mul_nonneg (Real.cosh_pos a).le (Real.sinh_pos_iff.mpr hb).le)
    dsimp [F]
    linarith only [hmul]
  have hstrict := hupper.trans_lt hFbound
  by_contra! hle
  have hreverse := Real.cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngle_nonneg a c b) (by linarith : Real.pi - 2 * α ≤ Real.pi) hle
  exact (not_lt_of_ge hreverse) hstrict

end Poincare.Alexandrov
