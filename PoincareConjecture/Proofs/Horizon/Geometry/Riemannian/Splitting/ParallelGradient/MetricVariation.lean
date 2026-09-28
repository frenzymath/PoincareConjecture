import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.AlongCurve.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Variation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem fderiv_flow_metric_pairing_eq_zero
    {q : P → E} {G : E → E} {B : E → E →L[ℝ] E →L[ℝ] ℝ} {p : P}
    (hq : ContDiffAt ℝ ∞ q p) (hG : DifferentiableAt ℝ G (q p))
    (hB : DifferentiableAt ℝ B (q p)) (τ : P)
    (htime : (fun z => fderiv ℝ q z τ) =ᶠ[𝓝 p] G ∘ q)
    (hmetric : ∀ v w : E,
      fderiv ℝ B (q p) (G (q p)) v w +
        B (q p) (fderiv ℝ G (q p) v) w + B (q p) v (fderiv ℝ G (q p) w) = 0)
    (v w : P) :
    fderiv ℝ (fun z => B (q z) (fderiv ℝ q z v) (fderiv ℝ q z w)) p τ = 0 := by
  have hqd := (hq.differentiableAt (by simp)).hasFDerivAt
  have hD := ((hq.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hd (d : P) : HasFDerivAt (fun z => fderiv ℝ q z d)
      ((fderiv ℝ (fderiv ℝ q) p).flip d) p := by
    simpa using hD.clm_apply (hasFDerivAt_const d p)
  have hlin (d : P) : fderiv ℝ (fderiv ℝ q) p τ d =
      fderiv ℝ G (q p) (fderiv ℝ q p d) := by
    have heq := htime.fderiv_eq (𝕜 := ℝ)
    rw [(hd τ).fderiv, (hG.hasFDerivAt.comp p hqd).fderiv] at heq
    have heqd := congrArg (fun L => L d) heq
    rw [(hq.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)).eq τ d]
    exact heqd
  have hBq : HasFDerivAt (fun z => B (q z))
      ((fderiv ℝ B (q p)).comp (fderiv ℝ q p)) p := hB.hasFDerivAt.comp p hqd
  have hm := (hBq.clm_apply (hd v)).clm_apply (hd w)
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply, hlin, htime.self_of_nhds, Function.comp_def]
  have h := hmetric (fderiv ℝ q p v) (fderiv ℝ q p w)
  linarith



theorem hasDerivAt_flow_metric_pairing_eq_zero
    {q : ℝ × E → E} {G : E → E} {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    {t : ℝ} {x : E} (hq : ContDiffAt ℝ ∞ q (t, x))
    (hG : DifferentiableAt ℝ G (q (t, x))) (hB : DifferentiableAt ℝ B (q (t, x)))
    (htime : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s => q (s, y)) (G (q (t, y))) t)
    (hmetric : ∀ v w : E,
      fderiv ℝ B (q (t, x)) (G (q (t, x))) v w +
        B (q (t, x)) (fderiv ℝ G (q (t, x)) v) w +
        B (q (t, x)) v (fderiv ℝ G (q (t, x)) w) = 0) (v w : E) :
    HasDerivAt (fun s => B (q (s, x))
      (fderiv ℝ (fun y => q (s, y)) x v) (fderiv ℝ (fun y => q (s, y)) x w)) 0 t := by
  have hqx : DifferentiableAt ℝ (fun y => q (t, y)) x :=
    (hq.differentiableAt (by simp)).comp x
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hcomp := (hG.hasFDerivAt.comp x hqx.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hcomp
  have hv := CoordinateExponential.hasDerivAt_variation hq htime v
  have hw := CoordinateExponential.hasDerivAt_variation hq htime w
  rw [hcomp] at hv hw
  have hBq : HasDerivAt (fun s => B (q (s, x)))
      (fderiv ℝ B (q (t, x)) (G (q (t, x)))) t :=
    hB.hasFDerivAt.comp_hasDerivAt t htime.self_of_nhds
  have hm := (hBq.clm_apply hv).clm_apply hw
  apply hm.congr_deriv
  have h := hmetric (fderiv ℝ (fun y => q (t, y)) x v)
    (fderiv ℝ (fun y => q (t, y)) x w)
  simp only [ContinuousLinearMap.comp_apply, add_apply] at ⊢
  linarith

end PoincareConjecture
