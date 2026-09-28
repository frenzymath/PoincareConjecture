import PoincareConjecture.Proofs.M60.Mathlib.ComplexGradient
import PoincareConjecture.Proofs.M60.Mathlib.ComplexEuclideanOperator
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Coordinates










set_option autoImplicit false

open Complex
open scoped ContDiff

namespace PoincareConjecture.M60

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)



noncomputable def complexConnectionOperator (B : E →L[ℝ] E →L[ℝ] E) (a b : E) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  -(1 / 2 : ℝ) • (complexifyEuclideanOperator n (B a) +
    I • complexifyEuclideanOperator n (B b))



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




noncomputable def harmonicComplexOperator (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (u : ℂ → E) (z : ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  complexConnectionOperator (Γ (u z)) (fderiv ℝ u z 1) (fderiv ℝ u z I)




theorem contDiffAt_harmonicComplexOperator
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : ℂ → E} {z : ℂ}
    (hΓ : ContDiffAt ℝ 1 Γ (u z)) (hu : ContDiffAt ℝ 2 u z) :
    ContDiffAt ℝ 1 (harmonicComplexOperator Γ u) z := by
  have hG := hΓ.comp z (hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
  have hdu := hu.fderiv_right (m := 1) (by norm_num)
  have hc (d : ℂ) := (complexifyEuclideanOperator n).contDiff.contDiffAt.comp z
    (hG.clm_apply (hdu.clm_apply (contDiffAt_const (c := d))))
  exact ((hc 1).add ((hc I).const_smul I)).const_smul (-(1 / 2 : ℝ))




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

end PoincareConjecture.M60
