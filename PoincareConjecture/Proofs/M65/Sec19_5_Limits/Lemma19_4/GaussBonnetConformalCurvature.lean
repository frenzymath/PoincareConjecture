import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalConnectionTrace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M65Gauss

private theorem conformal_metric_pair
    {h : RiemannianMetric 2 LoopPlane} {x : LoopPlane} {c : ℝ}
    (hc : ∀ i j : Fin 2,
      h.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) = if i = j then c else 0)
    (v : LoopPlane) (k : Fin 2) :
    h.euclideanCoefficients x v (EuclideanSpace.basisFun (Fin 2) ℝ k) = c * v k := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hv : v = ∑ i : Fin 2, e.repr v i • e i := (e.sum_repr v).symm
  have hp (i : Fin 2) : h.euclideanCoefficients x (e i) (e k) =
      if i = k then c else 0 := hc i k
  nth_rw 1 [hv]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  change (∑ i : Fin 2, e.repr v i * h.euclideanCoefficients x (e i) (e k)) = c * v k
  simp_rw [hp]
  fin_cases k <;> simp [e, mul_comm]

theorem connectionCoefficient_conformal_log
    {h : RiemannianMetric 2 LoopPlane} (D : LeviCivitaData h)
    {x : LoopPlane} {c : LoopPlane → ℝ} (hc : DifferentiableAt ℝ c x)
    (hcpos : 0 < c x)
    (hconf : ∀ᶠ y in 𝓝 x, ∀ i j : Fin 2,
      h.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) = if i = j then c y else 0)
    (i j k : Fin 2) :
    connectionCoefficient D x (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) k =
      (if j = k then fderiv ℝ (fun y => Real.log (c y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ i) / 2 else 0) +
      (if i = k then fderiv ℝ (fun y => Real.log (c y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ j) / 2 else 0) -
      (if i = j then fderiv ℝ (fun y => Real.log (c y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ k) / 2 else 0) := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hp (a b d : Fin 2) :
      fderiv ℝ (fun y => h.euclideanCoefficients y (e a) (e b)) x (e d) =
        if a = b then fderiv ℝ c x (e d) else 0 := by
    have he : (fun y => h.euclideanCoefficients y (e a) (e b)) =ᶠ[𝓝 x]
        (fun y => if a = b then c y else 0) := hconf.mono fun y hy => hy a b
    rw [he.fderiv_eq]
    split_ifs <;> simp
  have hk := D.inner_connection_const x (e i) (e j) (e k)
  change 2 * h.euclideanCoefficients x (connectionCoefficient D x (e i) (e j)) (e k) =
    fderiv ℝ (fun y => h.euclideanCoefficients y (e j) (e k)) x (e i) +
    fderiv ℝ (fun y => h.euclideanCoefficients y (e k) (e i)) x (e j) -
    fderiv ℝ (fun y => h.euclideanCoefficients y (e i) (e j)) x (e k) at hk
  rw [conformal_metric_pair hconf.self_of_nhds, hp, hp, hp] at hk
  simp only [fderiv.log hc hcpos.ne', smul_apply, smul_eq_mul]
  dsimp only [e] at hk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hk ⊢ <;>
    field_simp [hcpos.ne'] <;> nlinarith

private theorem fderiv_coordinate {F : LoopPlane → LoopPlane} {x : LoopPlane}
    (hF : DifferentiableAt ℝ F x) (u : LoopPlane) (k : Fin 2) :
    (fderiv ℝ F x u) k = fderiv ℝ (fun y => F y k) x u := by
  have hd := (EuclideanSpace.proj k).hasFDerivAt.comp x hF.hasFDerivAt
  exact (congrArg (fun L => L u) hd.fderiv).symm

theorem curvatureTensor_conformal_log
    {h : RiemannianMetric 2 LoopPlane} (D : LeviCivitaData h)
    {U : Set LoopPlane} (hU : IsOpen U) {x : LoopPlane} (hx : x ∈ U)
    {c : LoopPlane → ℝ} (hc : ContDiffOn ℝ ∞ c U)
    (hcpos : ∀ y ∈ U, 0 < c y)
    (hconf : ∀ y ∈ U, ∀ i j : Fin 2,
      h.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) = if i = j then c y else 0) :
    D.curvatureTensor x (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) / c x =
      -(∑ i : Fin 2, fderiv ℝ (fun y =>
        fderiv ℝ (fun z => Real.log (c z)) y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          x (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2 := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let l := fun y => Real.log (c y)
  let p (i : Fin 2) (y : LoopPlane) := fderiv ℝ l y (e i) / 2
  have hl : ContDiffAt ℝ ∞ l x :=
    ((hc x hx).contDiffAt (hU.mem_nhds hx)).log (hcpos x hx).ne'
  have hdl : DifferentiableAt ℝ (fderiv ℝ l) x :=
    (hl.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hcoef (y : LoopPlane) (hy : y ∈ U) (i j k : Fin 2) :
      connectionCoefficient D y (e i) (e j) k =
        (if j = k then p i y else 0) + (if i = k then p j y else 0) -
          (if i = j then p k y else 0) :=
    connectionCoefficient_conformal_log D
      (((hc y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      (hcpos y hy) (Filter.Eventually.mono (hU.mem_nhds hy) fun z hz => hconf z hz) i j k
  have h11 : (fun y => D.euclideanConnection (e 1) (e 1) y 0) =ᶠ[𝓝 x]
      (fun y => -p 0 y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa [connectionCoefficient_apply] using hcoef y hy 1 1 0
  have h01 : (fun y => D.euclideanConnection (e 0) (e 1) y 0) =ᶠ[𝓝 x]
      (p 1) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa [connectionCoefficient_apply] using hcoef y hy 0 1 0
  have hd11 : (fderiv ℝ (D.euclideanConnection (e 1) (e 1)) x (e 0)) 0 =
      -fderiv ℝ (p 0) x (e 0) := by
    rw [fderiv_coordinate ((D.contDiffAt_euclideanConnection x (e 1) (e 1)).differentiableAt
      (by simp)), h11.fderiv_eq, fderiv_fun_neg]
    rfl
  have hd01 : (fderiv ℝ (D.euclideanConnection (e 0) (e 1)) x (e 1)) 0 =
      fderiv ℝ (p 1) x (e 1) := by
    rw [fderiv_coordinate ((D.contDiffAt_euclideanConnection x (e 0) (e 1)).differentiableAt
      (by simp)), h01.fderiv_eq]
  have hv (v : LoopPlane) : v = v 0 • e 0 + v 1 • e 1 := by
    ext i
    fin_cases i <;> simp [e, EuclideanSpace.basisFun_apply]
  have hquad :
      (connectionCoefficient D x (e 0) (connectionCoefficient D x (e 1) (e 1))) 0 -
        (connectionCoefficient D x (e 1) (connectionCoefficient D x (e 0) (e 1))) 0 = 0 := by
    nth_rw 1 [hv (connectionCoefficient D x (e 1) (e 1))]
    nth_rw 1 [hv (connectionCoefficient D x (e 0) (e 1))]
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [hcoef x hx, Fin.isValue, reduceIte]
    ring
  have hcurv : (show LoopPlane from D.curvature x (e 0) (e 1) (e 1)) 0 =
      -fderiv ℝ (p 0) x (e 0) - fderiv ℝ (p 1) x (e 1) := by
    rw [D.curvature_eq_euclideanConnection]
    simp only [PiLp.add_apply, PiLp.sub_apply, hd11, hd01]
    change -fderiv ℝ (p 0) x (e 0) +
      connectionCoefficient D x (e 0) (connectionCoefficient D x (e 1) (e 1)) 0 -
      (fderiv ℝ (p 1) x (e 1) +
        connectionCoefficient D x (e 1) (connectionCoefficient D x (e 0) (e 1)) 0) = _
    linarith
  have hpd (i : Fin 2) : fderiv ℝ (p i) x (e i) =
      fderiv ℝ (fun y => fderiv ℝ l y (e i)) x (e i) / 2 := by
    have hd := (hdl.clm_apply (differentiableAt_const (e i))).hasFDerivAt.mul_const ((2 : ℝ)⁻¹)
    simpa only [p, div_eq_mul_inv, smul_apply, smul_eq_mul, mul_comm] using
      congrArg (fun L => L (e i)) hd.fderiv
  change h.euclideanCoefficients x (D.curvature x (e 0) (e 1) (e 1)) (e 0) / c x = _
  rw [conformal_metric_pair (hconf x hx), hcurv, hpd, hpd]
  rw [mul_div_cancel_left₀ _ (hcpos x hx).ne']
  simp only [Fin.sum_univ_two, l, e]
  ring

end PoincareConjecture.M65Gauss
