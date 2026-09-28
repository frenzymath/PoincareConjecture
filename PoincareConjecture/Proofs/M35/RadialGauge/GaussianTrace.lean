import PoincareConjecture.Proofs.M35.RadialGauge.GaussianEuclidean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem integral_stdGaussian_covector_trace
    {q : V → V →L[ℝ] F} {q' : V → V →L[ℝ] V →L[ℝ] F}
    (hq : Continuous q) (hq' : Continuous q')
    (hd : ∀ z, HasFDerivAt q (q' z) z)
    {C D : ℝ} (hb : ∀ z, ‖q z‖ ≤ C) (hdb : ∀ z, ‖q' z‖ ≤ D) :
    (∫ z, q z z ∂stdGaussian V) =
      ∫ z, ∑ i : Fin (n + 1), q' z (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ)) ∂stdGaussian V := by
  let e (i : Fin (n + 1)) := EuclideanSpace.single i (1 : ℝ)
  have he (i : Fin (n + 1)) : ‖e i‖ = 1 := by simp [e]
  have hqi (i : Fin (n + 1)) :
      Integrable (fun z : V => z i • q z) (stdGaussian V) := by
    apply (IsGaussian.integrable_id.norm.mul_const C).mono'
      (((show Continuous (fun z : V => z i) by fun_prop).smul hq).aestronglyMeasurable)
    exact Eventually.of_forall (fun z => by
      change ‖z i • q z‖ ≤ ‖z‖ * C
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le z i) (hb z) (norm_nonneg _) (norm_nonneg _))
  have hdi (i : Fin (n + 1)) : Integrable (fun z => q' z (e i)) (stdGaussian V) := by
    apply (integrable_const D).mono' (hq'.clm_apply continuous_const).aestronglyMeasurable
    exact Eventually.of_forall (fun z => by
      simpa only [he i, mul_one] using ((q' z).le_opNorm (e i)).trans
        (mul_le_mul_of_nonneg_right (hdb z) (norm_nonneg (e i))))
  have hqa (i : Fin (n + 1)) :
      Integrable (fun z : V => z i • (q z (e i))) (stdGaussian V) := by
    exact (ContinuousLinearMap.apply ℝ F (e i)).integrable_comp (hqi i)
  have hda (i : Fin (n + 1)) :
      Integrable (fun z => q' z (e i) (e i)) (stdGaussian V) :=
    (ContinuousLinearMap.apply ℝ F (e i)).integrable_comp (hdi i)
  have hp (i : Fin (n + 1)) :
      (∫ z : V, z i • q z (e i) ∂stdGaussian V) =
        ∫ z, q' z (e i) (e i) ∂stdGaussian V := by
    have h := congrArg (fun p : V →L[ℝ] F => p (e i))
      (integral_stdGaussian_coordinate_derivative i hq hq' hd hb hdb)
    rw [ContinuousLinearMap.integral_apply (hdi i),
      ContinuousLinearMap.integral_apply (hqi i)] at h
    simpa only [smul_apply] using h.symm
  have hrepr (z : V) : ∑ i, z i • e i = z := by
    simpa only [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr z
  calc
    _ = ∫ z, ∑ i : Fin (n + 1), z i • q z (e i) ∂stdGaussian V := by
      apply integral_congr_ae
      refine Eventually.of_forall (fun z => ?_)
      change q z z = ∑ i, z i • q z (e i)
      calc
        _ = q z (∑ i, z i • e i) := by rw [hrepr]
        _ = _ := by simp only [map_sum, map_smul]
    _ = ∑ i : Fin (n + 1), ∫ z, z i • q z (e i) ∂stdGaussian V :=
      integral_finsetSum _ (fun i _ => hqa i)
    _ = ∑ i : Fin (n + 1), ∫ z, q' z (e i) (e i) ∂stdGaussian V := by
      exact Finset.sum_congr rfl (fun i _ => hp i)
    _ = _ := (integral_finsetSum _ (fun i _ => hda i)).symm

end PoincareConjecture.M35.RadialGauge
