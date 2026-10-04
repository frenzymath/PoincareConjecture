import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Complex.Gradient
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Complex.EuclideanOperator
import PoincareLib.Geometry.Riemannian.Connection.Variation.Coordinates

/-!
# The actual first-order system for a harmonic coordinate map

The branch-isolation argument in Sacks-Uhlenbeck Theorem 1.6, printed
p. 5, writes the complex gradient as a solution of a linear covariant
Cauchy-Riemann equation. Its coefficient is constructed from the actual
smooth Christoffel form and actual first derivatives of the displayed map.
-/

set_option autoImplicit false

open Complex
open scoped ContDiff

namespace PoincareMT.M60

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The complex connection matrix determined by the two real derivative
columns. Source: SU Theorem 1.6, p. 5, local-frame derivation. -/
noncomputable def complexConnectionOperator (B : E →L[ℝ] E →L[ℝ] E) (a b : E) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  -(1 / 2 : ℝ) • (complexifyEuclideanOperator n (B a) +
    I • complexifyEuclideanOperator n (B b))

/-- Symmetry of the actual Christoffel form cancels the mixed complex
terms. Source: SU Theorem 1.6, p. 5, local-frame derivation. -/
theorem complexConnectionOperator_apply (B : E →L[ℝ] E →L[ℝ] E) (a b : E)
    (hsym : B a b = B b a) :
    complexConnectionOperator B a b (complexCoordinates n a - I • complexCoordinates n b) =
      -(1 / 2 : ℝ) • complexCoordinates n (B a a + B b b) := by
  change -(1 / 2 : ℝ) •
      (complexifyEuclideanOperator n (B a) (complexCoordinates n a - I • complexCoordinates n b) +
        I • complexifyEuclideanOperator n (B b)
          (complexCoordinates n a - I • complexCoordinates n b)) = _
  simp only [map_sub, map_smul, complexifyEuclideanOperator_real,
    smul_sub, smul_smul, I_mul_I, neg_one_smul, sub_neg_eq_add, hsym, map_add]
  congr 1
  abel

/-- The coefficient in the complex-gradient equation is a literal
function of the Christoffel form and the displayed map. Source:
SU Theorem 1.6, p. 5, local-frame derivation. -/
noncomputable def harmonicComplexOperator (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (u : ℂ → E) (z : ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  complexConnectionOperator (Γ (u z)) (fderiv ℝ u z 1) (fderiv ℝ u z I)

/-- The constructed coefficient is C1 wherever the coordinate map is
C2 and the Christoffel form is C1. Source: SU Theorem 1.6, p. 5,
local-frame regularity derivation. -/
theorem contDiffAt_harmonicComplexOperator
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : ℂ → E} {z : ℂ}
    (hΓ : ContDiffAt ℝ 1 Γ (u z)) (hu : ContDiffAt ℝ 2 u z) :
    ContDiffAt ℝ 1 (harmonicComplexOperator Γ u) z := by
  have hG := hΓ.comp z (hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
  have hdu := hu.fderiv_right (m := 1) (by norm_num)
  have hc (d : ℂ) := (complexifyEuclideanOperator n).contDiff.contDiffAt.comp z
    (hG.clm_apply (hdu.clm_apply (contDiffAt_const (c := d))))
  exact ((hc 1).add ((hc I).const_smul I)).const_smul (-(1 / 2 : ℝ))

/-- The actual covariant harmonic equation implies the actual linear
complex-gradient equation, including zero derivatives. Source:
SU Theorem 1.6, p. 5, local branch-isolation derivation. -/
theorem complexGradient_equation_of_covDeriv
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : ℂ → E} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z)
    (hsym : ∀ a b : E, Γ (u z) a b = Γ (u z) b a)
    (hτ : ConnectionVariation.covDerivAlong Γ u (fun w => fderiv ℝ u w 1) 1 z +
      ConnectionVariation.covDerivAlong Γ u (fun w => fderiv ℝ u w I) I z = 0) :
    cauchyRiemannDerivative (complexGradient (complexCoordinates n) u) z =
      harmonicComplexOperator Γ u z (complexGradient (complexCoordinates n) u z) := by
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hd (d : ℂ) : fderiv ℝ (fun w => fderiv ℝ u w d) z d =
      fderiv ℝ (fderiv ℝ u) z d d := by
    rw [fderiv_clm_apply hdu (differentiableAt_const d)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  simp only [ConnectionVariation.covDerivAlong, hd] at hτ
  have he : fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z I I =
      -(Γ (u z) (fderiv ℝ u z 1) (fderiv ℝ u z 1) +
        Γ (u z) (fderiv ℝ u z I) (fderiv ℝ u z I)) := by
    apply eq_neg_of_add_eq_zero_left
    convert hτ using 1
    abel
  rw [cauchyRiemannDerivative_complexGradient _ hu, he]
  change _ = complexConnectionOperator _ _ _ _
  rw [complexGradient, complexConnectionOperator_apply _ _ _ (hsym _ _), map_neg,
    smul_neg, neg_smul]

end PoincareMT.M60
