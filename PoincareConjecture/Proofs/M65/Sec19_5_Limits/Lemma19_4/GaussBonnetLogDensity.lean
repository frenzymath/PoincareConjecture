import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetConformalCurvature
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetNormalDensity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussEquation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace PoincareConjecture.M65Gauss

private theorem conformalGram_pairing
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane} {c : ℝ}
    (hconf : m60AreaGram g F x = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (v w : LoopPlane) :
    g.euclideanCoefficients (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) =
      c * inner ℝ v w := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have he (i j : Fin 2) :
      g.euclideanCoefficients (F x) (fderiv ℝ F x (e i)) (fderiv ℝ F x (e j)) =
        if i = j then c else 0 := by
    have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hconf
    simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using! hh
  have hv (a : LoopPlane) : a = a 0 • e 0 + a 1 • e 1 := by
    ext i
    fin_cases i <;> simp [e, EuclideanSpace.basisFun_apply]
  have hin : inner ℝ v w = v 0 * w 0 + v 1 * w 1 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  rw [hin]
  conv_lhs => rw [hv v, hv w]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  change w 0 * (v 0 * g.euclideanCoefficients (F x) (fderiv ℝ F x (e 0))
      (fderiv ℝ F x (e 0)) + v 1 * g.euclideanCoefficients (F x)
        (fderiv ℝ F x (e 1)) (fderiv ℝ F x (e 0))) +
    w 1 * (v 0 * g.euclideanCoefficients (F x) (fderiv ℝ F x (e 0))
      (fderiv ℝ F x (e 1)) + v 1 * g.euclideanCoefficients (F x)
        (fderiv ℝ F x (e 1)) (fderiv ℝ F x (e 1))) = _
  rw [he, he, he, he]
  norm_num
  ring






theorem logarithmicDensity_eq_gauss
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) {F : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {U : Set LoopPlane} (hU : IsOpen U) {x : LoopPlane} (hx : x ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) {c : LoopPlane → ℝ}
    (hc : ContDiffOn ℝ ∞ c U) (hcpos : ∀ y ∈ U, 0 < c y)
    (hconf : ∀ y ∈ U, m60AreaGram g F y = c y • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ;
    -(∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ (fun z => Real.log (c z)) y (e i))
        x (e i)) / 2 =
      (D.curvatureTensor (F x) (fderiv ℝ F x (e 0)) (fderiv ℝ F x (e 1))
        (fderiv ℝ F x (e 0)) (fderiv ℝ F x (e 1)) +
        g.inner (F x) (normalHessian D F x (e 0) (e 0))
          (normalHessian D F x (e 1) (e 1)) -
        g.inner (F x) (normalHessian D F x (e 0) (e 1))
          (normalHessian D F x (e 0) (e 1))) / c x := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let δ : LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ := innerSL ℝ
  let B (y : LoopPlane) : LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ := c y • δ
  have hB : ContDiffOn ℝ ∞ B U := by
    exact ((ContinuousLinearMap.id ℝ ℝ).smulRight δ).contDiff.comp_contDiffOn hc
  have hBs (y : LoopPlane) (_hy : y ∈ U) (v w : LoopPlane) : B y v w = B y w v := by
    change c y * inner ℝ v w = c y * inner ℝ w v
    rw [real_inner_comm v w]
  have hBp (y : LoopPlane) (hy : y ∈ U) (v : LoopPlane) (hv : v ≠ 0) :
      0 < B y v v := by
    exact mul_pos (hcpos y hy) (real_inner_self_pos.mpr hv)
  obtain ⟨h, Ds, V, hV, hxV, hVU, heq⟩ :=
    RiemannianMetric.exists_local_realization hU hx B hB hBs hBp
  have hFs : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hF y hy).contDiffAt (hU.mem_nhds hy)
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ v w,
      h.inner y v w = g.inner (F y) (fderiv ℝ F y v) (fderiv ℝ F y w) := by
    filter_upwards [hV.mem_nhds hxV] with y hy v w
    change h.euclideanCoefficients y v w =
      g.euclideanCoefficients (F y) (fderiv ℝ F y v) (fderiv ℝ F y w)
    rw [heq y hy]
    exact (conformalGram_pairing (hconf y (hVU hy)) v w).symm
  have hconfh (y : LoopPlane) (hy : y ∈ V) (i j : Fin 2) :
      h.euclideanCoefficients y (e i) (e j) = if i = j then c y else 0 := by
    rw [heq y hy]
    change c y * inner ℝ (e i) (e j) = _
    simp only [e.inner_eq_ite, mul_ite, mul_one, mul_zero]
  have hR := curvatureTensor_conformal_log Ds hV hxV (hc.mono hVU)
    (fun y hy => hcpos y (hVU hy)) hconfh
  have hN (i j : Fin 2) : secondFundamentalForm D Ds F x (e i) (e j) =
      normalHessian D F x (e i) (e j) :=
    secondFundamentalForm_eq_projection_hessian D Ds hFs.self_of_nhds hmetric
      (hcpos x hx) (hconf x hx) (e i) (e j)
  have hG := gauss_curvatureTensor D Ds hFs hmetric (e 0) (e 1) (e 0) (e 1)
  rw [secondFundamentalForm_symm D Ds hFs.self_of_nhds (e 1) (e 0), hN, hN, hN] at hG
  exact hR.symm.trans (congrArg (fun t : ℝ => t / c x) hG)

end PoincareConjecture.M65Gauss
