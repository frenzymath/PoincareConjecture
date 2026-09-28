import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.CovariantTest
import PoincareConjecture.Proofs.M04.TensorNormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem abs_twoTensor_pair_le_of_normSq (g : RiemannianMetric n V)
    {H : V → (Fin 2 → V) → ℝ} (hH : IsSmoothCovariantTensor H)
    {δ : ℝ} (hδ : 0 ≤ δ) (x u v : V) (hbound : (g.tensorNorm H x) ^ 2 ≤ δ ^ 2) :
    |H x ![u, v]| ≤ δ * (g.inner x u u + g.inner x v v + 1) := by
  have hu : 0 ≤ g.inner x u u := by
    by_cases hz : u = 0
    · simp [hz]
    · exact (g.pos x u hz).le
  have hv : 0 ≤ g.inner x v v := by
    by_cases hz : v = 0
    · simp [hz]
    · exact (g.pos x v hz).le
  have he := M04.tensorEvaluation_sq_le_tensorNorm g hH x ![u, v]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  have hsmall := he.trans (mul_le_mul_of_nonneg_right hbound (mul_nonneg hu hv))
  have hweights : g.inner x u u * g.inner x v v ≤
      (g.inner x u u + g.inner x v v + 1) ^ 2 := by
    nlinarith [sq_nonneg (g.inner x u u), sq_nonneg (g.inner x v v), mul_nonneg hu hv]
  have hs : |H x ![u, v]| ^ 2 ≤ (δ * (g.inner x u u + g.inner x v v + 1)) ^ 2 := by
    rw [sq_abs, mul_pow]
    exact hsmall.trans (mul_le_mul_of_nonneg_left hweights (sq_nonneg δ))
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hδ (by linarith))).mp hs

theorem exists_tensor_pair_test_bound (g : RiemannianMetric n V)
    {a : V → ℝ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    {U W : V → V} (hU : ContDiff ℝ ∞ U) (hW : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : V → (Fin 2 → V) → ℝ,
      IsSmoothCovariantTensor H → ∀ δ : ℝ, 0 ≤ δ →
      (∀ x ∈ tsupport a, (g.tensorNorm H x) ^ 2 ≤ δ ^ 2) →
      |∫ x, a x * H x ![U x, W x]| ≤ C * δ := by
  let weight := fun x => |a x| * (g.inner x (U x) (U x) + g.inner x (W x) (W x) + 1)
  have hg := contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hweight : Continuous weight := ha.continuous.abs.mul
    (((hg.clm_apply hU).clm_apply hU).continuous.add
      ((hg.clm_apply hW).clm_apply hW).continuous |>.add continuous_const)
  have hweightc : HasCompactSupport weight := hac.abs.mul_right
  have hweightI : Integrable weight := hweight.integrable_of_hasCompactSupport hweightc
  have hnonneg (x : V) : 0 ≤ weight x := by
    have hu : 0 ≤ g.inner x (U x) (U x) := by
      by_cases hz : U x = 0
      · simp [hz]
      · exact (g.pos x _ hz).le
    have hw : 0 ≤ g.inner x (W x) (W x) := by
      by_cases hz : W x = 0
      · simp [hz]
      · exact (g.pos x _ hz).le
    exact mul_nonneg (abs_nonneg _) (by linarith)
  refine ⟨∫ x, weight x, integral_nonneg hnonneg, ?_⟩
  intro H hH δ hδ hbound
  have hI : Integrable (fun x => a x * H x ![U x, W x]) :=
    (ha.continuous.mul (smooth_twoTensor_pair_contDiff hH hU hW).continuous
      ).integrable_of_hasCompactSupport hac.mul_right
  have hpoint (x : V) : |a x * H x ![U x, W x]| ≤ δ * weight x := by
    by_cases hx : x ∈ tsupport a
    · have he := mul_le_mul_of_nonneg_left
        (abs_twoTensor_pair_le_of_normSq g hH hδ x (U x) (W x) (hbound x hx)) (abs_nonneg (a x))
      rw [abs_mul]
      convert! he using 1
      dsimp only [weight]
      ring
    · have hz := image_eq_zero_of_notMem_tsupport hx
      simp only [hz, zero_mul, abs_zero, weight, mul_zero, le_refl]
  calc
    _ ≤ ∫ x, |a x * H x ![U x, W x]| := abs_integral_le_integral_abs
    _ ≤ ∫ x, δ * weight x := integral_mono hI.abs (hweightI.const_mul δ) hpoint
    _ = (∫ x, weight x) * δ := by rw [integral_const_mul, mul_comm]

end PoincareConjecture.M35.Uniqueness.Heat
