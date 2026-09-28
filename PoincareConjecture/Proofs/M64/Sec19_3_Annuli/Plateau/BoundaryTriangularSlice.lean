import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceHorizontalGreen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64Source_annulusPoint_contDiff (s : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => annulusPoint x s) := by
  have hfun : (fun x : ℝ => annulusPoint x s) = fun x => x • e0 + s • e1 := by
    funext x
    ext i
    fin_cases i <;> simp [annulusPoint]
  rw [hfun]
  exact (contDiff_id.smul contDiff_const).add contDiff_const

theorem m64TriangularSource_point
    {T : LoopPlane → LoopPlane} (hsecond : ∀ p, T p 1 = p 1) (x s : ℝ) :
    T (annulusPoint x s) = annulusPoint (T (annulusPoint x s) 0) s := by
  ext i
  fin_cases i
  · rfl
  · change T (annulusPoint x s) 1 = s
    exact hsecond _

def m64TriangularSourceSlice
    (T : LoopPlane ≃ₜ LoopPlane) (hsecond : ∀ p, T p 1 = p 1) (s : ℝ) : ℝ ≃ₜ ℝ where
  toFun x := T (annulusPoint x s) 0
  invFun x := T.symm (annulusPoint x s) 0
  left_inv x := by
    have h := congrArg (fun p : LoopPlane => p 0) (T.symm_apply_apply (annulusPoint x s))
    rw [m64TriangularSource_point hsecond] at h
    exact h
  right_inv x := by
    have h := congrArg (fun p : LoopPlane => p 0) (T.apply_symm_apply (annulusPoint x s))
    rw [m64TriangularSource_point (m64TriangularSource_inverse_second T hsecond)] at h
    exact h
  continuous_toFun :=
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous.comp
      (T.continuous.comp (m64Source_annulusPoint_contDiff s).continuous)
  continuous_invFun :=
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous.comp
      (T.symm.continuous.comp (m64Source_annulusPoint_contDiff s).continuous)

theorem m64TriangularSourceSlice_contDiff
    (T : LoopPlane ≃ₜ LoopPlane) (hsecond : ∀ p, T p 1 = p 1) (s : ℝ)
    (hT : ContDiff ℝ ∞ T) : ContDiff ℝ ∞ (m64TriangularSourceSlice T hsecond s) :=
  (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).contDiff.comp
    (hT.comp (m64Source_annulusPoint_contDiff s))

theorem m64TriangularSourceSlice_deriv
    (T : LoopPlane ≃ₜ LoopPlane) (hsecond : ∀ p, T p 1 = p 1)
    (hT : Differentiable ℝ T) (x s : ℝ) :
    deriv (m64TriangularSourceSlice T hsecond s) x = fderiv ℝ T (annulusPoint x s) e0 0 :=
  (m64Source_horizontalSlice_hasDerivAt hT x s).deriv

theorem m64Source_verticalSlice_hasDerivAt
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T) (x s : ℝ) :
    HasDerivAt (fun y => T (annulusPoint x y) 0)
      (fderiv ℝ T (annulusPoint x s) e1 0) s := by
  have hline : HasDerivAt (fun y : ℝ => annulusPoint x y) e1 s := by
    convert! ((hasDerivAt_id s).smul_const e1).const_add (x • e0) using 1
    · funext y
      ext i
      fin_cases i <;> simp [annulusPoint]
    · simp
  have hcurve := (hT (annulusPoint x s)).hasFDerivAt.comp_hasDerivAt s hline
  exact (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
    s hcurve

theorem m64TriangularCofactorTest0_fixed_seam
    (T : LoopPlane ≃ₜ LoopPlane) (hi : Differentiable ℝ T.symm) {x : ℝ}
    (hfix : ∀ s, T (annulusPoint x s) = annulusPoint x s)
    (phi : LoopPlane → ℝ) (s : ℝ) :
    m64TriangularCofactorTest0 T phi (annulusPoint x s) = 0 := by
  have hfixinv (y : ℝ) : T.symm (annulusPoint x y) = annulusPoint x y := by
    exact (congrArg T.symm (hfix y)).symm.trans (T.symm_apply_apply _)
  have hconst : (fun y : ℝ => T.symm (annulusPoint x y) 0) = fun _ => x := by
    funext y
    rw [hfixinv]
    rfl
  have hd := (m64Source_verticalSlice_hasDerivAt hi x s).deriv
  rw [hconst, deriv_const] at hd
  rw [m64TriangularCofactorTest0, m64Source_first_coordinate_derivative hi,
    ← hd, neg_zero, zero_mul]

end PoincareConjecture
