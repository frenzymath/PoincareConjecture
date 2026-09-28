import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.LieTestIntegral
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TensorTestBound
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem real_eq_zero_of_abs_le_every_positive_multiple {z C : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → |z| ≤ C * δ) : z = 0 := by
  have ht : Tendsto (fun δ : ℝ => C * δ) (𝓝[>] 0) (𝓝 (C * 0)) :=
    (continuous_const.mul continuous_id).continuousWithinAt
  have hz : |z| ≤ 0 := by
    simpa only [mul_zero] using ge_of_tendsto ht
      (eventually_mem_nhdsWithin.mono (fun δ hδ => h δ hδ))
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg z))

theorem integral_lie_eq_zero_of_small_defect_tests
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {B : V → V} (hB : ContDiff ℝ ∞ B)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (u v : V) (C : Fin n → ℝ)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ X : V → V, ContDiff ℝ ∞ X ∧
      (∀ x ∈ tsupport φ, (g.tensorNorm (killingDefectTensor D X) x) ^ 2 ≤ δ ^ 2) ∧
      ∀ k, |(∫ x, lieTestCoefficient D φ u v k x * X x k) -
        (∫ x, lieTestCoefficient D φ u v k x * B x k)| ≤ C k * δ) :
    (∫ x, φ x * DeTurckNative.metricLieDerivative D B x u v) = 0 := by
  obtain ⟨C₀, _hC₀, hb⟩ := exists_tensor_pair_test_bound g hφ hc
    (contDiff_const (c := u)) (contDiff_const (c := v))
  apply real_eq_zero_of_abs_le_every_positive_multiple (C := C₀ + ∑ k, C k)
  intro δ hδ
  obtain ⟨X, hX, hdefect, htest⟩ := happrox δ hδ
  have hsmall : |∫ x, φ x * DeTurckNative.metricLieDerivative D X x u v| ≤ C₀ * δ :=
    hb (killingDefectTensor D X) (isSmoothCovariantTensor_killingDefectTensor D X hX)
      δ hδ.le hdefect
  let IX := fun k => ∫ x, lieTestCoefficient D φ u v k x * X x k
  let IB := fun k => ∫ x, lieTestCoefficient D φ u v k x * B x k
  have hsum : |(∑ k, IX k) - ∑ k, IB k| ≤ (∑ k, C k) * δ := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun k _ => htest k).trans_eq (Finset.sum_mul ..).symm)
  rw [integral_metricLieDerivative_eq_tests D hX hφ hc] at hsmall
  rw [integral_metricLieDerivative_eq_tests D hB hφ hc]
  change |∑ k, IB k| ≤ _
  have htri := abs_sub (∑ k, IX k) ((∑ k, IX k) - ∑ k, IB k)
  have he : (∑ k, IX k) - ((∑ k, IX k) - ∑ k, IB k) = ∑ k, IB k := by ring
  rw [he] at htri
  calc
    _ ≤ |∑ k, IX k| + |(∑ k, IX k) - ∑ k, IB k| := htri
    _ ≤ C₀ * δ + (∑ k, C k) * δ := add_le_add hsmall hsum
    _ = (C₀ + ∑ k, C k) * δ := by ring

theorem metricLieDerivative_eq_zero_of_compact_tests
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {B : V → V} (hB : ContDiff ℝ ∞ B)
    (htest : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ u v : V, (∫ x, φ x * DeTurckNative.metricLieDerivative D B x u v) = 0) :
    ∀ x u v : V, DeTurckNative.metricLieDerivative D B x u v = 0 := by
  intro x u v
  have hcont : Continuous (fun y => DeTurckNative.metricLieDerivative D B y u v) :=
    (smooth_twoTensor_pair_contDiff (isSmoothCovariantTensor_killingDefectTensor D B hB)
      (contDiff_const (c := u)) (contDiff_const (c := v))).continuous
  have hae : ∀ᵐ y ∂volume, DeTurckNative.metricLieDerivative D B y u v = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
      (fun φ hφ hc => by simpa only [smul_eq_mul] using htest φ hφ hc u v)
  exact congrFun ((Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae) x

end PoincareConjecture.M35.Uniqueness.Heat
