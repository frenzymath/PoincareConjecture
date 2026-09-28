import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingKernel
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul











set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior



theorem averagingKernel_fderiv (r : ℝ) (z v : LoopPlane) :
    fderiv ℝ (averagingKernel r) z v =
      r⁻¹ ^ 3 * fderiv ℝ averagingProfile (r⁻¹ • z) v := by
  have hl : HasFDerivAt (fun w : LoopPlane => r⁻¹ • w)
      (r⁻¹ • ContinuousLinearMap.id ℝ LoopPlane) z := by
    simpa +instances only [Pi.smul_apply, id_eq] using! (hasFDerivAt_id z).const_smul r⁻¹
  have hρ : DifferentiableAt ℝ averagingProfile (r⁻¹ • z) :=
    ((EuclideanMollificationNative.mollifier_contDiff
    (by norm_num : (0 : ℝ) < 1)).differentiable (by simp)) (r⁻¹ • z)
  have hd := (hρ.hasFDerivAt.comp z hl).const_mul (r⁻¹ ^ 2)
  change HasFDerivAt (averagingKernel r) _ z at hd
  rw [hd.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring



theorem averagingKernel_radius_hasDerivAt {r : ℝ} (hr : r ≠ 0) (z : LoopPlane) :
    HasDerivAt (fun s => averagingKernel s z)
      (-2 * r⁻¹ * averagingKernel r z - r⁻¹ * fderiv ℝ (averagingKernel r) z z) r := by
  have hi : HasDerivAt (fun s : ℝ => s⁻¹) (-(r⁻¹ ^ 2)) r := by
    simpa only [inv_pow] using hasDerivAt_inv hr
  have hρ : DifferentiableAt ℝ averagingProfile (r⁻¹ • z) :=
    ((EuclideanMollificationNative.mollifier_contDiff
    (by norm_num : (0 : ℝ) < 1)).differentiable (by simp)) (r⁻¹ • z)
  have hc := hρ.hasFDerivAt.comp_hasDerivAt r (hi.smul_const z)
  have hd := (hi.pow 2).fun_mul hc
  change HasDerivAt (fun s => averagingKernel s z) _ r at hd
  apply hd.congr_deriv
  simp only [averagingKernel_fderiv, averagingKernel, map_smul, smul_eq_mul,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Function.comp_apply, Pi.pow_apply]
  ring





theorem averagingKernel_radius_weak_test {r : ℝ} (hr : r ≠ 0) (x z : LoopPlane) :
    HasDerivAt (fun s => averagingKernel s (x - z))
      (∑ i : Fin 2, fderiv ℝ (fun y : LoopPlane =>
        ((x i - y i) / r) * averagingKernel r (x - y)) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) r := by
  apply (averagingKernel_radius_hasDerivAt hr (x - z)).congr_deriv
  have hk : DifferentiableAt ℝ (averagingKernel r) (x - z) :=
    ((averagingKernel_contDiff r).differentiable (by simp)) (x - z)
  have harg : HasFDerivAt (fun y : LoopPlane => x - y)
      (0 - ContinuousLinearMap.id ℝ LoopPlane) z :=
    (hasFDerivAt_const x z).sub (hasFDerivAt_id z)
  have hkernel := hk.hasFDerivAt.comp z harg
  have hfield (i : Fin 2) :
      fderiv ℝ (fun y : LoopPlane => ((x i - y i) / r) * averagingKernel r (x - y)) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      -r⁻¹ * averagingKernel r (x - z) - ((x i - z i) / r) *
        fderiv ℝ (averagingKernel r) (x - z) (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    have hcoord := ((hasFDerivAt_const (𝕜 := ℝ) (x i) z).sub
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).mul_const r⁻¹
    have hd := hcoord.mul hkernel
    simp only [← div_eq_mul_inv] at hd
    change HasFDerivAt (fun y : LoopPlane =>
      ((x i - y i) / r) * averagingKernel r (x - y)) _ z at hd
    rw [hd.fderiv]
    simp [EuclideanSpace.basisFun_apply, div_eq_mul_inv]
    ring
  have hrepr : (∑ i : Fin 2, (x - z) i • EuclideanSpace.basisFun (Fin 2) ℝ i) = x - z :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr (x - z)
  have hlinear := congrArg (fderiv ℝ (averagingKernel r) (x - z)) hrepr
  simp only [Fin.sum_univ_two, map_add, map_smul, smul_eq_mul, PiLp.sub_apply] at hlinear
  rw [Fin.sum_univ_two, hfield 0, hfield 1, ← hlinear]
  ring

end PoincareConjecture.M65Interior
