import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic








set_option autoImplicit false

open Set MeasureTheory Function
open scoped ENNReal

namespace Poincare.MeasureTheory.GaussianMoment

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]


def shell (x : X) (r : ℝ) (j : ℕ) : Set X :=
  {y | (j : ℝ) * r ≤ dist x y ∧ dist x y < ((j : ℝ) + 1) * r}

theorem measurableSet_shell (x : X) (r : ℝ) (j : ℕ) :
    MeasurableSet (shell x r j) :=
  (measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable).inter
    (measurableSet_lt (continuous_const.dist continuous_id).measurable measurable_const)

omit [MeasurableSpace X] [BorelSpace X] in
theorem shell_subset_ball (x : X) (r : ℝ) (j : ℕ) :
    shell x r j ⊆ Metric.ball x (((j : ℝ) + 1) * r) := by
  intro y hy
  simpa only [Metric.mem_ball, dist_comm] using hy.2

omit [MeasurableSpace X] [BorelSpace X] in
theorem iUnion_shell (x : X) {r : ℝ} (hr : 0 < r) :
    ⋃ j : ℕ, shell x r j = univ := by
  apply eq_univ_of_forall
  intro y
  refine mem_iUnion.mpr ⟨⌊dist x y / r⌋₊, ?_⟩
  constructor
  · exact (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg dist_nonneg hr.le))
  · exact (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (dist x y / r))

omit [MeasurableSpace X] [BorelSpace X] in
theorem pairwiseDisjoint_shell (x : X) {r : ℝ} (hr : 0 < r) :
    Pairwise (Disjoint on shell x r) := by
  intro i j hij
  apply disjoint_left.mpr
  intro y hi hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    exact (not_lt_of_ge (hj.1.trans' (mul_le_mul_of_nonneg_right h hr.le))) hi.2
  · have h : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
    exact (not_lt_of_ge (hi.1.trans' (mul_le_mul_of_nonneg_right h hr.le))) hj.2



theorem integrable_of_shell_bounds (μ : Measure X) (x : X) {r : ℝ} (hr : 0 < r)
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (K D : ℕ → ℝ)
    (hfinite : ∀ j, μ (shell x r j) < ⊤)
    (hbound : ∀ j, ∀ y ∈ shell x r j, ‖f y‖ ≤ K j)
    (hKD : ∀ j, K j * μ.real (shell x r j) ≤ D j)
    (hD : Summable D) :
    Integrable f μ ∧ (∫ y, ‖f y‖ ∂μ) ≤ ∑' j, D j := by
  have hi : ∀ j, IntegrableOn f (shell x r j) μ := by
    intro j
    apply IntegrableOn.of_bound (hfinite j) hf.restrict (K j)
    exact (ae_restrict_iff' (measurableSet_shell x r j)).mpr
      (Filter.Eventually.of_forall (hbound j))
  have hle : ∀ j, (∫ y in shell x r j, ‖f y‖ ∂μ) ≤ D j := by
    intro j
    calc
      (∫ y in shell x r j, ‖f y‖ ∂μ) =
          ‖∫ y in shell x r j, ‖f y‖ ∂μ‖ :=
        (Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))).symm
      _ ≤ K j * μ.real (shell x r j) :=
        norm_setIntegral_le_of_norm_le_const (hfinite j)
          (fun y hy ↦ by simpa only [norm_norm] using hbound j y hy)
      _ ≤ D j := hKD j
  have hs : Summable (fun j ↦ ∫ y in shell x r j, ‖f y‖ ∂μ) :=
    hD.of_nonneg_of_le (fun _ ↦ integral_nonneg (fun _ ↦ norm_nonneg _)) hle
  have hint := integrableOn_iUnion_of_summable_integral_norm hi hs
  rw [iUnion_shell x hr, integrableOn_univ] at hint
  refine ⟨hint, ?_⟩
  have heq := integral_iUnion (measurableSet_shell x r)
    (pairwiseDisjoint_shell x hr) hint.norm.integrableOn
  rw [iUnion_shell x hr, setIntegral_univ] at heq
  rw [heq]
  exact hs.tsum_le_tsum hle hD

end Poincare.MeasureTheory.GaussianMoment
