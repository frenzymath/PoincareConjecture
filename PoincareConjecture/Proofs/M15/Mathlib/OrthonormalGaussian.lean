import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform










set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem Module.Basis.bilin_apply_equivFun_symm
    (b : Module.Basis (Fin n) ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (z : Fin n → ℝ) :
    B (b.equivFun.symm z) (b.equivFun.symm z) = ∑ i, z i ^ 2 := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul,
    sum_apply, smul_eq_mul]
  simp [hb, mul_ite, pow_two]

namespace MeasureTheory

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]



theorem integral_exp_neg_bilin_of_orthonormal_basis
    (b : Module.Basis (Fin n) ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    {c : ℝ} (hc : 0 < c) :
    (∫ v, Real.exp (-c * B v v) ∂Measure.map b.equivFun.symm volume) =
      Real.rpow (Real.pi / c) ((n : ℝ) / 2) := by
  let e := b.equivFun.toContinuousLinearEquiv.symm
  change (∫ v, Real.exp (-c * B v v) ∂Measure.map e.toHomeomorph volume) = _
  rw [e.toHomeomorph.measurableEmbedding.integral_map]
  change (∫ z : Fin n → ℝ,
    Real.exp (-c * B (b.equivFun.symm z) (b.equivFun.symm z))) = _
  simp_rw [b.bilin_apply_equivFun_symm B hb]
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin n)) hc
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at h
  simpa [EuclideanSpace.real_norm_sq_eq] using h




theorem integrable_exp_neg_bilin_of_orthonormal_basis
    (b : Module.Basis (Fin n) ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun v => Real.exp (-c * B v v))
      (Measure.map b.equivFun.symm volume) := by
  by_contra h
  have hvalue := integral_exp_neg_bilin_of_orthonormal_basis b B hb hc
  rw [integral_undef h] at hvalue
  exact (ne_of_gt (Real.rpow_pos_of_pos (div_pos Real.pi_pos hc) _)) hvalue.symm

end MeasureTheory
