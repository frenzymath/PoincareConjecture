import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem fderiv_metric_eq_christoffel
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (hinv : (B x).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v, B y u v = B y v u) (a b c : E) :
    fderiv ℝ B x c a b =
      B x (coordinateChristoffel B x c a) b +
        B x a (coordinateChristoffel B x c b) := by
  have hD (u v d : E) :
      fderiv ℝ (fun y => B y u v) x d = fderiv ℝ B x d u v := by
    have h := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
      (hasFDerivAt_const v x)
    simpa using congrArg (fun L => L d) h.fderiv
  have hK (u v w : E) :
      B x (coordinateChristoffel B x u v) w =
        (2⁻¹ : ℝ) * (fderiv ℝ B x u v w + fderiv ℝ B x v w u -
          fderiv ℝ B x w u v) := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L w)
      (hinv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B x) u v))
    simpa [coordinateChristoffel, metricKoszulCovector] using h
  have hsymm' (u v w : E) : fderiv ℝ B x u v w = fderiv ℝ B x u w v := by
    rw [← hD v w u, ← hD w v u]
    have heq : (fun y => B y v w) =ᶠ[𝓝 x] (fun y => B y w v) :=
      hsymm.mono (fun y hy => hy v w)
    exact congrArg (fun L : E →L[ℝ] ℝ => L u) heq.fderiv_eq
  rw [hsymm.self_of_nhds a (coordinateChristoffel B x c b),
    hK c a b, hK c b a, hsymm' c b a, hsymm' a b c, hsymm' b a c]
  ring



theorem hasDerivWithinAt_metric_parallel
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q V W : ℝ → E} {S : Set ℝ} {t : ℝ}
    (hB : DifferentiableAt ℝ B (q t)) (hinv : (B (q t)).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 (q t), ∀ u v, B y u v = B y v u)
    (hq : DifferentiableAt ℝ q t)
    (hV : HasDerivWithinAt V
      (-coordinateChristoffel B (q t) (deriv q t) (V t)) S t)
    (hW : HasDerivWithinAt W
      (-coordinateChristoffel B (q t) (deriv q t) (W t)) S t) :
    HasDerivWithinAt (fun s => B (q s) (V s) (W s)) 0 S t := by
  have hmetric : HasDerivWithinAt (fun s => B (q s))
      (fderiv ℝ B (q t) (deriv q t)) S t :=
    HasFDerivAt.comp_hasDerivWithinAt (l := B) (f := q) t
      hB.hasFDerivAt hq.hasDerivAt.hasDerivWithinAt
  have hleft : HasDerivWithinAt (fun s => B (q s) (V s))
      (B (q t) (-coordinateChristoffel B (q t) (deriv q t) (V t)) +
        fderiv ℝ B (q t) (deriv q t) (V t)) S t := by
    simpa only [add_comm] using hmetric.clm_apply hV
  have hd : HasDerivWithinAt (fun s => B (q s) (V s) (W s))
      (B (q t) (V t) (-coordinateChristoffel B (q t) (deriv q t) (W t)) +
        (B (q t) (-coordinateChristoffel B (q t) (deriv q t) (V t)) +
          fderiv ℝ B (q t) (deriv q t) (V t)) (W t)) S t := by
    simpa only [add_comm] using hleft.clm_apply hW
  convert hd using 1
  simp only [add_apply, map_neg, neg_apply]
  rw [fderiv_metric_eq_christoffel hB hinv hsymm]
  ring

end PoincareConjecture.CoordinateExponential
