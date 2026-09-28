import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RadialFlipGeometry
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

def m64HorizontalSource (tau : ℝ ≃ₜ ℝ) : LoopPlane ≃ₜ LoopPlane where
  toFun p := annulusPoint (tau (p 0)) (p 1)
  invFun p := annulusPoint (tau.symm (p 0)) (p 1)
  left_inv p := by ext i; fin_cases i <;> simp [annulusPoint]
  right_inv p := by ext i; fin_cases i <;> simp [annulusPoint]
  continuous_toFun := by unfold annulusPoint; fun_prop
  continuous_invFun := by unfold annulusPoint; fun_prop

theorem m64HorizontalSource_point (tau : ℝ ≃ₜ ℝ) (x s : ℝ) :
    m64HorizontalSource tau (annulusPoint x s) = annulusPoint (tau x) s := by
  simp [m64HorizontalSource, annulusPoint]

theorem m64HorizontalSource_symm (tau : ℝ ≃ₜ ℝ) :
    (m64HorizontalSource tau).symm = m64HorizontalSource tau.symm := rfl

theorem m64HorizontalSource_contDiff {tau : ℝ ≃ₜ ℝ} {q : WithTop ℕ∞}
    (ht : ContDiff ℝ q tau) : ContDiff ℝ q (m64HorizontalSource tau) := by
  have hfun : (m64HorizontalSource tau : LoopPlane → LoopPlane) =
      fun p => tau (p 0) • e0 + p 1 • e1 := by
    funext p
    ext i
    fin_cases i <;> simp [m64HorizontalSource, annulusPoint]
  rw [hfun]
  exact ((ht.comp (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).contDiff).smul
    (contDiff_const : ContDiff ℝ q (fun _ : LoopPlane => e0))).add
    ((EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).contDiff.smul
      (contDiff_const : ContDiff ℝ q (fun _ : LoopPlane => e1)))

theorem m64HorizontalSource_preimage_interior {tau : ℝ ≃ₜ ℝ}
    (ht : StrictMono tau) (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod) :
    m64HorizontalSource tau ⁻¹' S = S := by
  ext p
  simp only [mem_preimage, m64AnnulusInterior_coordinates]
  change (0 < tau (p 0) ∧ tau (p 0) < curvePeriod ∧ 0 < p 1 ∧ p 1 < 1) ↔ _
  have hlo : 0 < tau (p 0) ↔ 0 < p 0 := by
    simpa only [h0] using (ht.lt_iff_lt (a := 0) (b := p 0))
  have hhi : tau (p 0) < curvePeriod ↔ p 0 < curvePeriod := by
    simpa only [hP] using (ht.lt_iff_lt (a := p 0) (b := curvePeriod))
  rw [hlo, hhi]

theorem m64HorizontalSource_image_interior {tau : ℝ ≃ₜ ℝ}
    (ht : StrictMono tau) (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod) :
    m64HorizontalSource tau '' S = S := by
  calc
    _ = m64HorizontalSource tau '' (m64HorizontalSource tau ⁻¹' S) :=
      congrArg (fun U => m64HorizontalSource tau '' U)
        (m64HorizontalSource_preimage_interior ht h0 hP).symm
    _ = S := image_preimage_eq _ (m64HorizontalSource tau).surjective

def m64HorizontalSourceDerivative (a : ℝ) : LoopPlane →L[ℝ] LoopPlane :=
  (a • (EuclideanSpace.proj 0)).smulRight e0 + (EuclideanSpace.proj 1).smulRight e1

theorem m64HorizontalSourceDerivative_apply (a : ℝ) (v : LoopPlane) :
    m64HorizontalSourceDerivative a v = annulusPoint (a * v 0) (v 1) := by
  ext i
  fin_cases i <;> simp [m64HorizontalSourceDerivative, annulusPoint]

theorem m64HorizontalSource_hasFDerivAt {tau : ℝ ≃ₜ ℝ} {p : LoopPlane}
    (ht : DifferentiableAt ℝ tau (p 0)) :
    HasFDerivAt (m64HorizontalSource tau)
      (m64HorizontalSourceDerivative (deriv tau (p 0))) p := by
  have h0 := ht.hasDerivAt.comp_hasFDerivAt p
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).hasFDerivAt
  have h1 := (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).hasFDerivAt (x := p)
  have h := (h0.smul_const e0).add (h1.smul_const e1)
  convert! h using 1
  · funext q
    ext i
    fin_cases i <;> simp [m64HorizontalSource, annulusPoint]

theorem m64HorizontalSourceDerivative_det (a : ℝ) :
    (m64HorizontalSourceDerivative a).det = a := by
  change LinearMap.det (m64HorizontalSourceDerivative a).toLinearMap = a
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, m64HorizontalSourceDerivative_apply, annulusPoint]

theorem m64HorizontalSource_det {tau : ℝ ≃ₜ ℝ} {p : LoopPlane}
    (ht : DifferentiableAt ℝ tau (p 0)) :
    (fderiv ℝ (m64HorizontalSource tau) p).det = deriv tau (p 0) := by
  rw [(m64HorizontalSource_hasFDerivAt ht).fderiv, m64HorizontalSourceDerivative_det]

theorem m64HorizontalSource_fderiv_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {tau : ℝ ≃ₜ ℝ} (ht : Differentiable ℝ tau)
    {f : LoopPlane → E} (hf : Differentiable ℝ f) (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (f ∘ m64HorizontalSource tau) p (EuclideanSpace.single i 1) =
      (if i = 0 then deriv tau (p 0) else 1) •
        fderiv ℝ f (m64HorizontalSource tau p) (EuclideanSpace.single i 1) := by
  rw [fderiv_comp p (hf _) (m64HorizontalSource_hasFDerivAt (ht _)).differentiableAt,
    ContinuousLinearMap.comp_apply, (m64HorizontalSource_hasFDerivAt (ht _)).fderiv]
  have hb : m64HorizontalSourceDerivative (deriv tau (p 0)) (EuclideanSpace.single i 1) =
      (if i = 0 then deriv tau (p 0) else 1) • EuclideanSpace.single i 1 := by
    ext j
    fin_cases i <;> fin_cases j <;>
      simp [m64HorizontalSourceDerivative_apply, annulusPoint]
  rw [hb, map_smul]

theorem m64HorizontalSource_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {tau : ℝ ≃ₜ ℝ} (ht : Differentiable ℝ tau) (hpos : ∀ x, 0 < deriv tau x)
    (hmono : StrictMono tau) (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod)
    (f : LoopPlane → E) :
    (∫ p in S, deriv tau (p 0) • f (m64HorizontalSource tau p)) = ∫ p in S, f p := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume (s := S)
    isOpen_interior.measurableSet
    (fun p _ => (m64HorizontalSource_hasFDerivAt (ht (p 0))).hasFDerivWithinAt)
    (m64HorizontalSource tau).injective.injOn f
  rw [m64HorizontalSource_image_interior hmono h0 hP] at h
  simpa only [m64HorizontalSourceDerivative_det, abs_of_pos (hpos _)] using h.symm

end PoincareConjecture
