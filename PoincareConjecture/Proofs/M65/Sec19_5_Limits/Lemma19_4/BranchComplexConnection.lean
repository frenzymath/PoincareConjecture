import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchComplexGradient











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Complex
open scoped Topology ContDiff BigOperators

namespace PoincareConjecture.M65Branch

variable {n : ℕ}




def complexifyOperator :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
      ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun L => ContinuousLinearMap.pi fun k =>
      ∑ j : Fin n, ((L (EuclideanSpace.basisFun (Fin n) ℝ j)) k : ℂ) •
        ContinuousLinearMap.proj j
    map_add' := by
      intro L T
      ext v k
      simp only [add_apply, ContinuousLinearMap.pi_apply, sum_apply, smul_apply,
        ContinuousLinearMap.proj_apply, PiLp.add_apply, Pi.add_apply, ofReal_add,
        smul_eq_mul, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro r L
      ext v k
      simp only [smul_apply, ContinuousLinearMap.pi_apply, sum_apply,
        ContinuousLinearMap.proj_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul, ofReal_mul,
        RingHom.id_apply, Complex.real_smul, Finset.mul_sum, mul_assoc]
      }




theorem complexifyOperator_real
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    complexifyOperator L (coordinateComplexification v) =
      coordinateComplexification (L v) := by
  ext k
  change (∑ j : Fin n,
    ((L (EuclideanSpace.basisFun (Fin n) ℝ j)) k : ℂ) •
      (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ))
        (coordinateComplexification v) = ((L v) k : ℂ)
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  change (∑ j : Fin n,
    ((L (EuclideanSpace.basisFun (Fin n) ℝ j)) k : ℂ) * (v j : ℂ)) = ((L v) k : ℂ)
  have hv : ∑ j : Fin n, v j • EuclideanSpace.basisFun (Fin n) ℝ j = v :=
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  have hk := congrArg ((EuclideanSpace.proj k).comp L) hv
  simp only [map_sum, map_smul, smul_eq_mul] at hk
  have hkc := congrArg (fun r : ℝ => (r : ℂ)) hk
  simpa only [ofReal_sum, ofReal_mul, mul_comm, ContinuousLinearMap.comp_apply,
    EuclideanSpace.proj, PiLp.proj_apply] using hkc

variable {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}




def harmonicMatrix (D : LeviCivitaData g) (H : ℂ → EuclideanSpace ℝ (Fin n))
    (z : ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  (-(2 : ℂ)⁻¹) •
    (complexifyOperator (M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z 1)) +
      I • complexifyOperator (M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z I)))



theorem contDiffOn_harmonicMatrix (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {s : Set ℂ}
    (hs : IsOpen s) (hH : ContDiffOn ℝ ∞ H s) :
    ContDiffOn ℝ 1 (harmonicMatrix D H) s := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ H) s :=
    hH.fderiv_of_isOpen hs (WithTop.coe_le_coe.mpr le_top)
  have hC : ContDiffOn ℝ 1 (fun z => M65Gauss.connectionCoefficient D (H z)) s :=
    ((M65Gauss.contDiff_connectionCoefficient D).comp_contDiffOn hH).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hpart (v : ℂ) : ContDiffOn ℝ 1 (fun z =>
      complexifyOperator (M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z v))) s :=
    complexifyOperator.contDiff.comp_contDiffOn (hC.clm_apply (hD.clm_apply contDiffOn_const))
  exact ((hpart 1).add ((hpart I).const_smul I)).const_smul (-(2 : ℂ)⁻¹)




theorem harmonicMatrix_apply_gradient (D : LeviCivitaData g)
    (H : ℂ → EuclideanSpace ℝ (Fin n)) (z : ℂ) :
    harmonicMatrix D H z (complexGradient H z) = (-(2 : ℂ)⁻¹) •
      coordinateComplexification
        (M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1) +
          M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z I) (fderiv ℝ H z I)) := by
  unfold harmonicMatrix
  rw [smul_apply]
  congr 1
  simp only [complexGradient, smul_apply, add_apply, map_sub, map_smul,
    complexifyOperator_real]
  rw [M65Gauss.connectionCoefficient_symm D (H z) (fderiv ℝ H z I) (fderiv ℝ H z 1)]
  simp only [map_add, smul_add, smul_smul, I_mul_I, neg_one_smul]
  module

end PoincareConjecture.M65Branch
