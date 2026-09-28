import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetProjection
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussMapConnection
import PoincareConjecture.Definitions.M60Area










noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology ContDiff Manifold BigOperators

namespace PoincareConjecture.M65Gauss

open M65Branch

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
  {h : RiemannianMetric 2 LoopPlane}




def conformalTangentProjection (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (F : LoopPlane → EuclideanSpace ℝ (Fin n)) (x : LoopPlane) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  twoPlaneProjection (g.euclideanCoefficients (F x))
    (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 2) ℝ 0))
    (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 2) ℝ 1))




theorem conformalTangentProjection_fixes
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane} {c : ℝ}
    (hc : 0 < c) (hconf : m60AreaGram g F x = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (v : LoopPlane) : conformalTangentProjection g F x (fderiv ℝ F x v) = fderiv ℝ F x v := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have he (i j : Fin 2) : g.inner (F x) (fderiv ℝ F x (e i)) (fderiv ℝ F x (e j)) =
      if i = j then c else 0 := by
    have hh := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G i j) hconf
    simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, e] using! hh
  have h00 : g.inner (F x) (fderiv ℝ F x (e 0)) (fderiv ℝ F x (e 0)) = c := by
    simpa using he 0 0
  have h01 : g.inner (F x) (fderiv ℝ F x (e 0)) (fderiv ℝ F x (e 1)) = 0 := by
    simpa using he 0 1
  have h11 : g.inner (F x) (fderiv ℝ F x (e 1)) (fderiv ℝ F x (e 1)) = c := by
    simpa using he 1 1
  have hfix := twoPlaneProjection_fixes (g.euclideanCoefficients (F x))
    (fun v w => g.symm (F x) v w)
    (a := fderiv ℝ F x (e 0)) (b := fderiv ℝ F x (e 1))
    (h00.trans_ne hc.ne') h01 (h11.trans h00.symm)
  have hcol (i : Fin 2) : conformalTangentProjection g F x (fderiv ℝ F x (e i)) =
      fderiv ℝ F x (e i) := by
    fin_cases i
    · exact hfix.1
    · exact hfix.2
  conv_lhs => rw [← e.sum_repr v]
  simp only [map_sum, map_smul, hcol]
  simpa only [map_sum, map_smul] using congrArg (fderiv ℝ F x) (e.sum_repr v)




theorem differentiableAt_conformalTangentProjection
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane}
    (hF : ContDiffAt ℝ ∞ F x)
    (hne : g.inner (F x) (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≠ 0) :
    DifferentiableAt ℝ (conformalTangentProjection g F) x := by
  have hG : ContDiffAt ℝ ∞ (fun y => g.euclideanCoefficients (F y)) x :=
    (g.contDiffAt_euclideanCoefficients (F x)).comp x hF
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ F) x := hF.fderiv_right (by simp)
  have ha := hD.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 2) ℝ 0))
  have hb := hD.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hGa := hG.clm_apply ha
  have hGb := hG.clm_apply hb
  have hP := ((hGa.clm_apply ha).inv hne).smul
    ((hGa.smulRight ha).add (hGb.smulRight hb))
  exact hP.differentiableAt (by simp)




theorem secondFundamentalForm_eq_projection_hessian
    (D : LeviCivitaData g) (Ds : LeviCivitaData h)
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane}
    (hF : ContDiffAt ℝ ∞ F x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    {c : ℝ} (hc : 0 < c)
    (hconf : m60AreaGram g F x = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (u v : LoopPlane) :
    secondFundamentalForm D Ds F x u v = covariantHessianMap D F x u v -
      conformalTangentProjection g F x (covariantHessianMap D F x u v) := by
  let P := conformalTangentProjection g F x
  have hPB : P (secondFundamentalForm D Ds F x u v) = 0 := by
    have hn (w : LoopPlane) : g.euclideanCoefficients (F x) (fderiv ℝ F x w)
        (secondFundamentalForm D Ds F x u v) = 0 := by
      exact (g.symm (F x) _ _).trans (secondFundamentalForm_normal D Ds hF hmetric u v w)
    dsimp only [P, conformalTangentProjection]
    rw [twoPlaneProjection_apply]
    rw [hn, hn]
    simp only [zero_smul, add_zero, smul_zero]
  have hPT := conformalTangentProjection_fixes hc hconf (connectionCoefficient Ds x u v)
  change P (fderiv ℝ F x (connectionCoefficient Ds x u v)) = _ at hPT
  rw [secondFundamentalForm, map_sub, hPT] at hPB
  have he := sub_eq_zero.mp hPB
  change covariantHessianMap D F x u v - fderiv ℝ F x (connectionCoefficient Ds x u v) = _
  rw [← he]




theorem secondFundamentalForm_eq_projection_derivative
    (D : LeviCivitaData g) (Ds : LeviCivitaData h)
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane}
    (hF : ContDiffAt ℝ ∞ F x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (hconf : ∀ᶠ y in 𝓝 x, ∃ c : ℝ, 0 < c ∧
      m60AreaGram g F y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (u v : LoopPlane) :
    secondFundamentalForm D Ds F x u v =
      fderiv ℝ (conformalTangentProjection g F) x u (fderiv ℝ F x v) +
        connectionCoefficient D (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) -
          conformalTangentProjection g F x
            (connectionCoefficient D (F x) (fderiv ℝ F x u) (fderiv ℝ F x v)) := by
  obtain ⟨c, hc, hx⟩ := hconf.self_of_nhds
  have h00 : g.inner (F x) (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = c := by
    have hh := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G 0 0) hx
    simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one] using! hh
  have hP := differentiableAt_conformalTangentProjection hF (h00.trans_ne hc.ne')
  have hfix : ∀ᶠ y in 𝓝 x,
      conformalTangentProjection g F y (fderiv ℝ F y v) = fderiv ℝ F y v := by
    filter_upwards [hconf] with y hy
    obtain ⟨d, hd, hy⟩ := hy
    exact conformalTangentProjection_fixes hd hy v
  have hn := normal_second_derivative_eq_projection_derivative hP
    (show ContDiffAt ℝ 2 F x from hF.of_le (WithTop.coe_le_coe.mpr le_top)) u v hfix
  rw [secondFundamentalForm_eq_projection_hessian D Ds hF hmetric hc hx,
    covariantHessianMap, map_add]
  rw [← hn]
  abel





theorem norm_secondFundamentalForm_le_projection_derivative
    (D : LeviCivitaData g) (Ds : LeviCivitaData h)
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane}
    (hF : ContDiffAt ℝ ∞ F x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (hconf : ∀ᶠ y in 𝓝 x, ∃ c : ℝ, 0 < c ∧
      m60AreaGram g F y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (u v : LoopPlane) :
    ‖secondFundamentalForm D Ds F x u v‖ ≤
      ‖fderiv ℝ (conformalTangentProjection g F) x u‖ * ‖fderiv ℝ F x v‖ +
        (1 + ‖conformalTangentProjection g F x‖) * ‖connectionCoefficient D (F x)‖ *
          ‖fderiv ℝ F x u‖ * ‖fderiv ℝ F x v‖ := by
  let P := conformalTangentProjection g F x
  let Q := fderiv ℝ (conformalTangentProjection g F) x u
  let C := connectionCoefficient D (F x)
  let a := fderiv ℝ F x u
  let b := fderiv ℝ F x v
  rw [secondFundamentalForm_eq_projection_derivative D Ds hF hmetric hconf]
  change ‖Q b + C a b - P (C a b)‖ ≤
    ‖Q‖ * ‖b‖ + (1 + ‖P‖) * ‖C‖ * ‖a‖ * ‖b‖
  calc
    _ ≤ ‖Q b‖ + ‖C a b‖ + ‖P (C a b)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖Q‖ * ‖b‖ + ‖C‖ * ‖a‖ * ‖b‖ + ‖P‖ * (‖C‖ * ‖a‖ * ‖b‖) := by
      apply add_le_add
      · exact add_le_add (Q.le_opNorm b) (C.le_opNorm₂ a b)
      · exact (P.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (C.le_opNorm₂ a b) (norm_nonneg _))
    _ = _ := by ring

end PoincareConjecture.M65Gauss
