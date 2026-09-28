import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Defs
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Coordinates

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def koszulBilinear
    (A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  (2⁻¹ : ℝ) • (A + (flipL.comp A).flip - flipL.comp A.flip)

def christoffelBilinear (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (B x).inverse).comp
    (koszulBilinear (fderiv ℝ B x))

@[simp] theorem christoffelBilinear_apply
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) :
    christoffelBilinear B x u v = coordinateChristoffel B x u v := rfl

theorem contDiffAt_christoffelBilinear [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : ContDiffAt ℝ ∞ B x) (hinv : (B x).IsInvertible) :
    ContDiffAt ℝ ∞ (christoffelBilinear B) x := by
  have hi : ContDiffAt ℝ ∞ (fun y => (B y).inverse) x :=
    hinv.contDiffAt_map_inverse.comp x hB
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ B) x := hB.fderiv_right (by simp)
  have hf : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff
  unfold christoffelBilinear koszulBilinear
  fun_prop

private theorem fderiv_bilinear_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : E → E →L[ℝ] E →L[ℝ] F} {x : E}
    (hA : DifferentiableAt ℝ A x) (a u v : E) :
    fderiv ℝ (fun y => A y u v) x a = fderiv ℝ A x a u v := by
  have h := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)
  rw [h.fderiv]
  simp

theorem christoffelBilinear_symm
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v, B y u v = B y v u) (u v : E) :
    christoffelBilinear B x u v = christoffelBilinear B x v u := by
  have hD (a b c : E) : fderiv ℝ B x a b c = fderiv ℝ B x a c b := by
    rw [← fderiv_bilinear_apply hB, ← fderiv_bilinear_apply hB]
    have heq : (fun y => B y b c) =ᶠ[𝓝 x] (fun y => B y c b) :=
      hsymm.mono fun y hy => hy b c
    exact congrArg (fun L : E →L[ℝ] ℝ => L a)
      heq.fderiv_eq
  change (B x).inverse (metricKoszulCovector (fderiv ℝ B x) u v) =
    (B x).inverse (metricKoszulCovector (fderiv ℝ B x) v u)
  congr 1
  ext w
  simp only [metricKoszulCovector, smul_apply,
    add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hD v w u, hD w u v, hD u v w]
  ring

theorem coordinateCurvature_eq_christoffelCurvature
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hA : DifferentiableAt ℝ (christoffelBilinear B) x) (u v w : E) :
    coordinateCurvature B x u v w =
      ConnectionVariation.christoffelCurvature (christoffelBilinear B) x u v w := by
  have happ (a b c : E) :
      fderiv ℝ (fun y => coordinateChristoffel B y b c) x a =
        fderiv ℝ (christoffelBilinear B) x a b c :=
    fderiv_bilinear_apply hA a b c
  simp only [coordinateCurvature, ConnectionVariation.christoffelCurvature,
    christoffelBilinear_apply, happ]
  abel

end PoincareConjecture.CoordinateExponential
