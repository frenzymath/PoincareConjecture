import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussMapConnection

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.M65Gauss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem covariantDerivativeAlongMap_curvature (D : LeviCivitaData g)
    {F W : E → EuclideanSpace ℝ (Fin n)} {x : E}
    (hF : ContDiffAt ℝ ∞ F x) (hW : ContDiffAt ℝ ∞ W x) (u v : E) :
    covariantDerivativeAlongMap D F (fun y => covariantDerivativeAlongMap D F W y v) x u -
      covariantDerivativeAlongMap D F (fun y => covariantDerivativeAlongMap D F W y u) x v =
    D.curvature (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) (W x) := by
  have hFd : DifferentiableAt ℝ F x := hF.differentiableAt (by simp)
  have hWd : DifferentiableAt ℝ W x := hW.differentiableAt (by simp)
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hdW : DifferentiableAt ℝ (fderiv ℝ W) x :=
    (hW.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hΓ := (contDiff_connectionCoefficient D).differentiable (by simp)
  have hΓF : DifferentiableAt ℝ (fun y => connectionCoefficient D (F y)) x :=
    (hΓ (F x)).comp x hFd
  have hiter (a b : E) :
      covariantDerivativeAlongMap D F (fun y => covariantDerivativeAlongMap D F W y b) x a =
        fderiv ℝ (fderiv ℝ W) x a b +
        (fderiv ℝ (connectionCoefficient D) (F x) (fderiv ℝ F x a)
          (fderiv ℝ F x b) (W x) +
        connectionCoefficient D (F x) (fderiv ℝ (fderiv ℝ F) x a b) (W x) +
        connectionCoefficient D (F x) (fderiv ℝ F x b) (fderiv ℝ W x a)) +
        connectionCoefficient D (F x) (fderiv ℝ F x a)
          (fderiv ℝ W x b + connectionCoefficient D (F x) (fderiv ℝ F x b) (W x)) := by
    have hleft := hdW.clm_apply (differentiableAt_const b)
    have hright := (hΓF.clm_apply (hdF.clm_apply (differentiableAt_const b))).clm_apply hWd
    simp only [covariantDerivativeAlongMap]
    rw [fderiv_fun_add hleft hright]
    rw [fderiv_clm_apply hdW (differentiableAt_const b)]
    rw [fderiv_clm_apply (hΓF.clm_apply (hdF.clm_apply (differentiableAt_const b))) hWd]
    rw [fderiv_clm_apply hΓF (hdF.clm_apply (differentiableAt_const b))]
    rw [fderiv_fun_comp x (hΓ (F x)) hFd]
    rw [fderiv_clm_apply hdF (differentiableAt_const b)]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      fderiv_const_apply, zero_apply, map_zero, zero_add]
    abel
  have hcoef (a b c : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (D.euclideanConnection b c) (F x) a =
        fderiv ℝ (connectionCoefficient D) (F x) a b c := by
    change fderiv ℝ (fun y => connectionCoefficient D y b c) (F x) a = _
    rw [fderiv_clm_apply ((hΓ (F x)).clm_apply (differentiableAt_const b))
      (differentiableAt_const c)]
    rw [fderiv_clm_apply (hΓ (F x)) (differentiableAt_const b)]
    simp
  have hsF := hF.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have hsW := hW.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hiter, hiter, D.curvature_eq_euclideanConnection, hcoef, hcoef]
  rw [hsF u v, hsW u v]
  simp only [map_add, ← connectionCoefficient_apply]
  abel

end PoincareConjecture.M65Gauss
