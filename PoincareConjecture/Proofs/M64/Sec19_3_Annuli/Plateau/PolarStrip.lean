import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.Analysis.SpecialFunctions.PolarCoord












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Proofs.M58



def m64MorreyPolarStrip (a : LoopPlane) (rho : ℝ) (p : LoopPlane) : LoopPlane :=
  a + (rho * Real.exp (-p 1)) • angularPoint (p 0 - Real.pi)



theorem m64MorreyPolarStrip_contDiff (a : LoopPlane) (rho : ℝ) :
    ContDiff ℝ ∞ (m64MorreyPolarStrip a rho) := by
  have h0 : ContDiff ℝ ∞ (fun p : LoopPlane => p 0) := by fun_prop
  have h1 : ContDiff ℝ ∞ (fun p : LoopPlane => p 1) := by fun_prop
  exact contDiff_const.add ((contDiff_const.mul h1.neg.exp).smul
    (contDiff_angularPoint.comp (h0.sub contDiff_const)))



theorem m64MorreyPolarStrip_fderiv (a : LoopPlane) (rho : ℝ) (p v : LoopPlane) :
    fderiv ℝ (m64MorreyPolarStrip a rho) p v =
      (-v 1 * (rho * Real.exp (-p 1))) • angularPoint (p 0 - Real.pi) +
        (v 0 * (rho * Real.exp (-p 1))) • angularVector (p 0 - Real.pi) := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have hr := h1.neg.exp.const_mul rho
  have ht := (hasDerivAt_angularPoint (p 0 - Real.pi)).hasFDerivAt.comp p (h0.sub_const Real.pi)
  have hh := (hasFDerivAt_const a p).add (hr.smul ht)
  change HasFDerivAt (m64MorreyPolarStrip a rho) _ p at hh
  rw [hh.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, neg_apply,
    EuclideanSpace.coe_proj, Function.comp_apply, Pi.neg_apply, smul_smul, zero_add]
  module



theorem m64MorreyPolarStrip_det (a : LoopPlane) (rho : ℝ) (p : LoopPlane) :
    (fderiv ℝ (m64MorreyPolarStrip a rho) p).det = (rho * Real.exp (-p 1)) ^ 2 := by
  change LinearMap.det (fderiv ℝ (m64MorreyPolarStrip a rho) p).toLinearMap = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    ContinuousLinearMap.coe_coe]
  change (fderiv ℝ (m64MorreyPolarStrip a rho) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 0 *
      (fderiv ℝ (m64MorreyPolarStrip a rho) p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) 1 -
    (fderiv ℝ (m64MorreyPolarStrip a rho) p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) 0 *
      (fderiv ℝ (m64MorreyPolarStrip a rho) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 1 = _
  simp only [m64MorreyPolarStrip_fderiv]
  simp [EuclideanSpace.basisFun_apply, angularPoint, angularVector]
  nlinarith [congrArg (fun t : ℝ => (rho * Real.exp (-p 1)) ^ 2 * t)
    (Real.sin_sq_add_cos_sq (p 0))]



theorem m64MorreyPolarStrip_mapsTo_closedBall (a : LoopPlane) {rho : ℝ} (hrho : 0 ≤ rho) :
    MapsTo (m64MorreyPolarStrip a rho) m64AnnulusDomain (Metric.closedBall a rho) := by
  intro p hp
  rw [Metric.mem_closedBall, dist_eq_norm]
  change ‖(a + (rho * Real.exp (-p 1)) • angularPoint (p 0 - Real.pi)) - a‖ ≤ rho
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hrho (Real.exp_pos _).le), norm_angularPoint, mul_one]
  exact mul_le_of_le_one_right hrho (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp.2.2.1))



theorem m64MorreyPolarStrip_jacobian_lower (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho)
    {p : LoopPlane} (hp : p ∈ m64AnnulusDomain) :
    (rho * Real.exp (-1)) ^ 2 ≤ |(fderiv ℝ (m64MorreyPolarStrip a rho) p).det| := by
  rw [m64MorreyPolarStrip_det, abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hp.2.2.2])) hrho.le



theorem m64MorreyPolarStrip_injOn (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) :
    InjOn (m64MorreyPolarStrip a rho) {p : LoopPlane | 0 < p 0 ∧ p 0 < curvePeriod} := by
  intro p hp q hq hpq
  have hp' : (rho * Real.exp (-p 1), p 0 - Real.pi) ∈ polarCoord.target := by
    change 0 < rho * Real.exp (-p 1) ∧ -Real.pi < p 0 - Real.pi ∧ p 0 - Real.pi < Real.pi
    change 0 < p 0 ∧ p 0 < curvePeriod at hp
    refine ⟨by positivity, ?_⟩
    unfold curvePeriod at hp
    constructor <;> linarith
  have hq' : (rho * Real.exp (-q 1), q 0 - Real.pi) ∈ polarCoord.target := by
    change 0 < rho * Real.exp (-q 1) ∧ -Real.pi < q 0 - Real.pi ∧ q 0 - Real.pi < Real.pi
    change 0 < q 0 ∧ q 0 < curvePeriod at hq
    refine ⟨by positivity, ?_⟩
    unfold curvePeriod at hq
    constructor <;> linarith
  have hpol : polarCoord.symm (rho * Real.exp (-p 1), p 0 - Real.pi) =
      polarCoord.symm (rho * Real.exp (-q 1), q 0 - Real.pi) := by
    apply loopPlaneEquivProd.symm.injective
    rw [loopPlaneEquivProd_symm_polar, loopPlaneEquivProd_symm_polar]
    exact add_left_cancel hpq
  have heq := polarCoord.symm.injOn hp' hq' hpol
  have hangle := congrArg Prod.snd heq
  have hradius := mul_left_cancel₀ hrho.ne' (congrArg Prod.fst heq)
  have hheight := neg_injective (Real.exp_injective hradius)
  ext i
  fin_cases i
  · change p 0 - Real.pi = q 0 - Real.pi at hangle
    change p 0 = q 0
    linarith
  · exact hheight



theorem m64MorreyPolarStrip_periodic (a : LoopPlane) (rho x s : ℝ) :
    m64MorreyPolarStrip a rho (annulusPoint (x + curvePeriod) s) =
      m64MorreyPolarStrip a rho (annulusPoint x s) := by
  change a + (rho * Real.exp (-s)) • angularPoint (x + curvePeriod - Real.pi) =
    a + (rho * Real.exp (-s)) • angularPoint (x - Real.pi)
  have ht : x + curvePeriod - Real.pi = (x - Real.pi) + 2 * Real.pi := by
    unfold curvePeriod
    ring
  rw [ht]
  congr 2
  ext i
  fin_cases i <;> simp [angularPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

end PoincareConjecture
