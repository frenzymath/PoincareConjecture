import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialHadamard
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap












set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]




theorem exists_binary_quadratic_coefficients
    (hdim : Module.finrank ℝ E = 2) (A : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ContDiff ℝ ∞ A) (hinj : Function.Injective (A 0))
    (hsymm : ∀ x y, A 0 x y = A 0 y x) :
    ∃ (L : (ℝ × ℝ) ≃L[ℝ] E) (a b c : ℝ × ℝ → ℝ),
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ c ∧
      a 0 ≠ 0 ∧ b 0 = 0 ∧ c 0 ≠ 0 ∧
      ∀ p, A (L p) (L p) (L p) =
        a p * p.1 ^ 2 + 2 * b p * p.1 * p.2 + c p * p.2 ^ 2 := by
  let B := (A 0).toBilinForm
  have hB : B.IsSymm := ⟨hsymm⟩
  have hsep : B.SeparatingLeft := by
    intro x hx
    apply hinj
    rw [map_zero]
    exact ContinuousLinearMap.ext hx
  obtain ⟨v, hv⟩ : ∃ v : Module.Basis (Fin 2) ℝ E, B.IsOrthoᵢ v := by
    obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
    refine ⟨v.reindex (finCongr hdim), ?_⟩
    intro i j hij
    change B ((v.reindex (finCongr hdim)) i) ((v.reindex (finCongr hdim)) j) = 0
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    exact hv ((finCongr hdim).symm.injective.ne hij)
  let L : (ℝ × ℝ) ≃L[ℝ] E :=
    ((LinearEquiv.finTwoArrow ℝ ℝ).symm.trans v.equivFun.symm).toContinuousLinearEquiv
  have hL (p : ℝ × ℝ) : L p = p.1 • v 0 + p.2 • v 1 := by
    simp [L, Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
  let a : ℝ × ℝ → ℝ := fun p => A (L p) (v 0) (v 0)
  let b : ℝ × ℝ → ℝ := fun p => (A (L p) (v 0) (v 1) + A (L p) (v 1) (v 0)) / 2
  let c : ℝ × ℝ → ℝ := fun p => A (L p) (v 1) (v 1)
  have hd (i j : Fin 2) : ContDiff ℝ ∞ (fun p => A (L p) (v i) (v j)) :=
    ((hA.comp L.contDiff).clm_apply contDiff_const).clm_apply contDiff_const
  refine ⟨L, a, b, c, hd 0 0, ((hd 0 1).add (hd 1 0)).div_const 2, hd 1 1,
    ?_, ?_, ?_, ?_⟩
  · simpa only [a, map_zero, B, ContinuousLinearMap.toBilinForm_apply] using
      hv.not_isOrtho_basis_self_of_separatingLeft hsep 0
  · have h01 : A 0 (v 0) (v 1) = 0 := hv (by decide : (0 : Fin 2) ≠ 1)
    have h10 : A 0 (v 1) (v 0) = 0 := hv (by decide : (1 : Fin 2) ≠ 0)
    simp only [b, map_zero, h01, h10, add_zero, zero_div]
  · simpa only [c, map_zero, B, ContinuousLinearMap.toBilinForm_apply] using
      hv.not_isOrtho_basis_self_of_separatingLeft hsep 1
  · intro p
    change A (L p) (L p) (L p) =
      A (L p) (v 0) (v 0) * p.1 ^ 2 +
        2 * ((A (L p) (v 0) (v 1) + A (L p) (v 1) (v 0)) / 2) * p.1 * p.2 +
          A (L p) (v 1) (v 1) * p.2 ^ 2
    generalize A (L p) = C
    simp only [hL p, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring




theorem exists_morse_quadratic_coefficients
    (hdim : Module.finrank ℝ E = 2) (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hzero : fderiv ℝ f 0 = 0) (hinj : Function.Injective (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (L : (ℝ × ℝ) ≃L[ℝ] E) (a b c : ℝ × ℝ → ℝ),
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ c ∧
      a 0 ≠ 0 ∧ b 0 = 0 ∧ c 0 ≠ 0 ∧
      ∀ p, f (L p) - f 0 =
        a p * p.1 ^ 2 + 2 * b p * p.1 * p.2 + c p * p.2 ^ 2 := by
  obtain ⟨A, hA, hAzero, hfactor⟩ := exists_smooth_quadratic_factor f hf hzero
  have hAi : Function.Injective (A 0) := by
    rw [hAzero]
    intro x y hxy
    apply hinj
    exact smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0) hxy
  have hAs (x y : E) : A 0 x y = A 0 y x := by
    rw [hAzero]
    exact congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
      ((hf.contDiffAt.isSymmSndFDerivAt (by
        simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eq x y)
  obtain ⟨L, a, b, c, ha, hb, hc, ha0, hb0, hc0, hform⟩ :=
    exists_binary_quadratic_coefficients hdim A hA hAi hAs
  exact ⟨L, a, b, c, ha, hb, hc, ha0, hb0, hc0, fun p =>
    (hfactor (L p)).symm.trans (hform p)⟩

end PoincareConjecture.M25.Topology3D
