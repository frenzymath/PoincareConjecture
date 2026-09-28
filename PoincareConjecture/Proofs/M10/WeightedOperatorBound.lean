import PoincareConjecture.Proofs.M10.WeightedOperatorFormula
import PoincareConjecture.Proofs.M10.NormalizedFrameBound
import Mathlib.Analysis.Normed.Operator.Bilinear









set_option autoImplicit false

open scoped ContDiff BigOperators

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable local instance operatorBoundBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance operatorBoundBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace


theorem trace_weightedMetricDual_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ f : E → ℝ} {x : E}
    (hB : ContDiffAt ℝ 1 B x) (hρ : DifferentiableAt ℝ ρ x) (hf : ContDiffAt ℝ 2 f x)
    (hi : (B x).IsInvertible) (C : E ≃L[ℝ] E)
    (hC : ∀ v w, B x (C v) (C w) = inner ℝ v w)
    {K D I G R P : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (hI : 0 ≤ I)
    (hG : 0 ≤ G) (_hR : 0 ≤ R) (hP : 0 ≤ P)
    (hDB : ‖fderiv ℝ B x‖ ≤ D) (hInv : ‖(B x).inverse‖ ≤ I)
    (hdf : ‖fderiv ℝ f x‖ ≤ G) (hρpos : 0 ≤ ρ x) (hρR : ρ x ≤ R)
    (hdρ : ‖fderiv ℝ ρ x‖ ≤ P)
    (hsecond : ∀ v, fderiv ℝ (fderiv ℝ f) x v v ≤ K * ‖v‖ ^ 2) :
    LinearMap.trace ℝ E (fderiv ℝ (weightedMetricDual B ρ f) x).toLinearMap ≤
      R * (Fintype.card ι : ℝ) * (K + D * I * G) * I + P * I * G := by
  let a := (B x).inverse (fderiv ℝ f x)
  have ha : ‖a‖ ≤ I * G :=
    ((B x).inverse.le_opNorm _).trans (mul_le_mul hInv hdf (norm_nonneg _) hI)
  have hframe (i : ι) : ‖C (b i)‖ ^ 2 ≤ I := by
    have h := normalized_metric_vector_norm_sq_le (B x) hi C hC (b i)
    simpa only [b.norm_eq_one, one_pow, mul_one] using h.trans
      (mul_le_mul_of_nonneg_right hInv (sq_nonneg ‖b i‖))
  have hterm (i : ι) :
      fderiv ℝ (fderiv ℝ f) x (C (b i)) (C (b i)) -
        fderiv ℝ B x (C (b i)) a (C (b i)) ≤ (K + D * I * G) * I := by
    let v := C (b i)
    have hq : |fderiv ℝ B x v a v| ≤ D * I * G * ‖v‖ ^ 2 := calc
      _ ≤ ‖fderiv ℝ B x v‖ * ‖a‖ * ‖v‖ := (fderiv ℝ B x v).le_opNorm₂ a v
      _ ≤ (D * ‖v‖) * (I * G) * ‖v‖ := by
        gcongr
        exact ((fderiv ℝ B x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right hDB (norm_nonneg v))
      _ = D * I * G * ‖v‖ ^ 2 := by ring
    calc
      _ ≤ (K + D * I * G) * ‖v‖ ^ 2 := by
        nlinarith [hsecond v, (abs_le.mp hq).1]
      _ ≤ (K + D * I * G) * I :=
        mul_le_mul_of_nonneg_left (hframe i) (by positivity)
  have hsum : (∑ i, (fderiv ℝ (fderiv ℝ f) x (C (b i)) (C (b i)) -
      fderiv ℝ B x (C (b i)) a (C (b i)))) ≤
      (Fintype.card ι : ℝ) * ((K + D * I * G) * I) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hterm i)
  have hlast : fderiv ℝ ρ x a ≤ P * I * G := calc
    _ ≤ |fderiv ℝ ρ x a| := le_abs_self _
    _ ≤ ‖fderiv ℝ ρ x‖ * ‖a‖ := (fderiv ℝ ρ x).le_opNorm a
    _ ≤ P * (I * G) := mul_le_mul hdρ ha (norm_nonneg _) hP
    _ = P * I * G := by ring
  rw [trace_weightedMetricDual_eq b hB hρ hf hi C hC]
  change ρ x * _ + fderiv ℝ ρ x a ≤ _
  have hproduct := (mul_le_mul_of_nonneg_left hsum hρpos).trans
    (mul_le_mul_of_nonneg_right hρR (by positivity))
  nlinarith [hproduct]

end PoincareConjecture.M10
