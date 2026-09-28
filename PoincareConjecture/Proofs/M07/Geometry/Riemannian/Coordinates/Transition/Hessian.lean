import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.ChangeCoordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem fderiv_bilinear_apply_transition
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (u v w : E) :
    fderiv ℝ (fun y => B y u v) x w = fderiv ℝ B x w u v := by
  have h := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)
  simpa using congrArg (fun L => L w) h.fderiv

private theorem fderiv_metric_pullback_transition
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C (f x))
    (hf : ContDiffAt ℝ ∞ f x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v))
    (a u v : E) :
    fderiv ℝ B x a u v =
      fderiv ℝ C (f x) (fderiv ℝ f x a) (fderiv ℝ f x u) (fderiv ℝ f x v) +
        C (f x) (fderiv ℝ (fderiv ℝ f) x a u) (fderiv ℝ f x v) +
        C (f x) (fderiv ℝ f x u) (fderiv ℝ (fderiv ℝ f) x a v) := by
  have hD := (hf.fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hf' : HasFDerivAt f (fderiv ℝ f x) x :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  have hc := hC.hasFDerivAt.comp x hf'
  have hd := (hc.clm_apply
    (hD.hasFDerivAt.clm_apply (hasFDerivAt_const u x))).clm_apply
    (hD.hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have heq : (fun y => B y u v) =ᶠ[𝓝 x]
      (fun y => C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) :=
    hmetric.mono fun y hy => hy u v
  rw [← fderiv_bilinear_apply_transition hB u v a, heq.fderiv_eq]
  simpa [add_comm, add_left_comm, add_assoc] using congrArg (fun L => L a) hd.fderiv

private theorem inner_coordinateChristoffel_transition
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hinv : (B x).IsInvertible) (u v w : E) :
    B x (coordinateChristoffel B x u v) w =
      (2⁻¹ : ℝ) * (fderiv ℝ B x u v w + fderiv ℝ B x v w u -
        fderiv ℝ B x w u v) := by
  have h := congrArg (fun L : E →L[ℝ] ℝ => L w)
    (hinv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B x) u v))
  simpa [coordinateChristoffel, metricKoszulCovector] using h

theorem coordinateChristoffel_change_coordinates_bilinear
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C (f x))
    (hBinv : (B x).IsInvertible) (hCinv : (C (f x)).IsInvertible)
    (hCsymm : ∀ u v, C (f x) u v = C (f x) v u)
    (hf : ContDiffAt ℝ ∞ f x) (hsurj : Function.Surjective (fderiv ℝ f x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) (u v : E) :
    fderiv ℝ f x (coordinateChristoffel B x u v) =
      fderiv ℝ (fderiv ℝ f) x u v +
        coordinateChristoffel C (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) := by
  apply hCinv.injective
  ext z
  obtain ⟨w, rfl⟩ := hsurj z
  rw [← hmetric.self_of_nhds, inner_coordinateChristoffel_transition hBinv]
  simp only [map_add, add_apply]
  rw [inner_coordinateChristoffel_transition hCinv]
  rw [fderiv_metric_pullback_transition hB hC hf hmetric,
    fderiv_metric_pullback_transition hB hC hf hmetric,
    fderiv_metric_pullback_transition hB hC hf hmetric]
  have hsecond := (hf.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    norm_cast)).eq u w
  rw [hsecond]
  rw [hCsymm (fderiv ℝ f x w), hCsymm (fderiv ℝ f x u),
    hCsymm (fderiv ℝ f x v)]
  have hs (a b : E) :
      fderiv ℝ (fderiv ℝ f) x a b = fderiv ℝ (fderiv ℝ f) x b a :=
    (hf.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      norm_cast)).eq a b
  rw [hs w v, hs v u, hs w u]
  ring

end PoincareConjecture

namespace PoincareConjecture.CoordinateTransition

open PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_eq_christoffel
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C (f x))
    (hBinv : (B x).IsInvertible) (hCinv : (C (f x)).IsInvertible)
    (_hBsymm : ∀ᶠ y in 𝓝 x, ∀ u v, B y u v = B y v u)
    (hCsymm : ∀ᶠ y in 𝓝 (f x), ∀ u v, C y u v = C y v u)
    (hf : ContDiffAt ℝ ∞ f x) (hsurj : Function.Surjective (fderiv ℝ f x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) (u v : E) :
    fderiv ℝ (fderiv ℝ f) x u v =
      fderiv ℝ f x (CoordinateExponential.christoffelBilinear B x u v) -
        CoordinateExponential.christoffelBilinear C (f x)
          (fderiv ℝ f x u) (fderiv ℝ f x v) := by
  exact eq_sub_iff_add_eq.mpr
    (coordinateChristoffel_change_coordinates_bilinear hB hC hBinv hCinv
      hCsymm.self_of_nhds hf hsurj hmetric u v).symm

theorem surjective_of_pullback_isInvertible [FiniteDimensional ℝ E]
    {B C : E →L[ℝ] E →L[ℝ] ℝ} {D : E →L[ℝ] E}
    (hB : B.IsInvertible)
    (hmetric : ∀ u v, B u v = C (D u) (D v)) : Function.Surjective D := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
  intro u v huv
  apply hB.injective
  ext w
  change D u = D v at huv
  rw [hmetric u w, hmetric v w, huv]

abbrev ChristoffelSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] E

noncomputable def transitionHessianPolynomial
    (z : ChristoffelSpace E ×
      (ChristoffelSpace E × (E →L[ℝ] E))) : ChristoffelSpace E :=
  (ContinuousLinearMap.compL ℝ E E E z.2.2).comp z.1 -
    (z.2.1).bilinearComp z.2.2 z.2.2

@[simp] theorem transitionHessianPolynomial_apply
    (A B : ChristoffelSpace E) (D : E →L[ℝ] E) (u v : E) :
    transitionHessianPolynomial (A, (B, D)) u v = D (A u v) - B (D u) (D v) := by
  rfl

theorem transitionHessianPolynomial_eq
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C (f x))
    (hBinv : (B x).IsInvertible) (hCinv : (C (f x)).IsInvertible)
    (hCsymm : ∀ u v, C (f x) u v = C (f x) v u)
    (hf : ContDiffAt ℝ ∞ f x) (hsurj : Function.Surjective (fderiv ℝ f x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) (u v : E) :
    transitionHessianPolynomial
        (CoordinateExponential.christoffelBilinear B x,
          (CoordinateExponential.christoffelBilinear C (f x), fderiv ℝ f x)) u v =
      fderiv ℝ (fderiv ℝ f) x u v := by
  rw [transitionHessianPolynomial_apply]
  rw [show (CoordinateExponential.christoffelBilinear B x) u v =
      coordinateChristoffel B x u v by rfl,
    show (CoordinateExponential.christoffelBilinear C (f x))
      (fderiv ℝ f x u) (fderiv ℝ f x v) =
      coordinateChristoffel C (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) by rfl]
  have h := coordinateChristoffel_change_coordinates_bilinear
    hB hC hBinv hCinv hCsymm hf hsurj hmetric u v
  rw [h]
  abel

theorem fderiv_fderiv_eq_transitionHessianPolynomial
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C (f x))
    (hBinv : (B x).IsInvertible) (hCinv : (C (f x)).IsInvertible)
    (hCsymm : ∀ u v, C (f x) u v = C (f x) v u)
    (hf : ContDiffAt ℝ ∞ f x) (hsurj : Function.Surjective (fderiv ℝ f x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) :
    fderiv ℝ (fderiv ℝ f) x = transitionHessianPolynomial
      (CoordinateExponential.christoffelBilinear B x,
        (CoordinateExponential.christoffelBilinear C (f x), fderiv ℝ f x)) := by
  ext u v
  exact (transitionHessianPolynomial_eq hB hC hBinv hCinv hCsymm hf hsurj hmetric u v).symm

theorem fderiv_fderiv_eq_transitionHessianPolynomial_on
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C V)
    (hBinv : ∀ x ∈ U, (B x).IsInvertible)
    (hCinv : ∀ y ∈ V, (C y).IsInvertible)
    (hCsymm : ∀ y ∈ V, ∀ u v, C y u v = C y v u)
    (hf : ContDiffOn ℝ ∞ f U) (hmap : MapsTo f U V)
    (hsurj : ∀ x ∈ U, Function.Surjective (fderiv ℝ f x))
    (hmetric : ∀ x ∈ U, ∀ u v,
      B x u v = C (f x) (fderiv ℝ f x u) (fderiv ℝ f x v))
    {x : E} (hx : x ∈ U) :
    fderiv ℝ (fderiv ℝ f) x = transitionHessianPolynomial
      (CoordinateExponential.christoffelBilinear B x,
        (CoordinateExponential.christoffelBilinear C (f x), fderiv ℝ f x)) := by
  exact fderiv_fderiv_eq_transitionHessianPolynomial
    ((hB.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    ((hC.contDiffAt (hV.mem_nhds (hmap hx))).differentiableAt (by simp))
    (hBinv x hx) (hCinv (f x) (hmap hx)) (hCsymm (f x) (hmap hx))
    (hf.contDiffAt (hU.mem_nhds hx)) (hsurj x hx)
    (Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hmetric y hy))

theorem contDiff_transitionHessianPolynomial
    [CompleteSpace E] [FiniteDimensional ℝ E] :
    ContDiff ℝ ∞ (transitionHessianPolynomial :
      ChristoffelSpace E × (ChristoffelSpace E × (E →L[ℝ] E)) → ChristoffelSpace E) := by
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  change ContDiff ℝ ∞ (fun z : ChristoffelSpace E ×
      (ChristoffelSpace E × (E →L[ℝ] E)) =>
    z.2.2 (z.1 u v) - z.2.1 (z.2.2 u) (z.2.2 v))
  fun_prop

end PoincareConjecture.CoordinateTransition

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_christoffelBilinear [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ x ∈ U, (B x).IsInvertible) :
    ContDiffOn ℝ ∞ (christoffelBilinear B) U := by
  intro x hx
  exact (contDiffAt_christoffelBilinear
    ((hB x hx).contDiffAt (hU.mem_nhds hx)) (hinv x hx)).contDiffWithinAt

end PoincareConjecture.CoordinateExponential
