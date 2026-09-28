import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SquareCompletion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition

noncomputable section

open Set Module
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus.Morse

private theorem bilinear_apply_planar_expansion
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E)
    (hsymm : B u v = B v u) (x y : ℝ) :
    B (x • u + y • v) (x • u + y • v) =
      B u u * x ^ 2 + 2 * B u v * x * y + B v v * y ^ 2 := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [← hsymm]
  ring

theorem exists_smooth_morse_coordinates_two
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcrit : fderiv ℝ f 0 = 0)
    (hH : Function.Bijective (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2))
        (EuclideanSpace ℝ (Fin 2))) (σ : Fin 2 → ℝ),
      (∀ i, σ i = -1 ∨ σ i = 1) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, f (e x) = f 0 + ∑ i : Fin 2, σ i * x i ^ 2 := by
  let B := quadraticFactor f
  let L := (B 0).toBilinForm
  have hsymm : L.IsSymm := ⟨fun v w => quadraticFactor_symmetric hf 0 v w⟩
  have hsep : L.SeparatingLeft := by
    intro x hx
    apply hH.1
    ext y
    have hxy := hx y
    change quadraticFactor f 0 x y = 0 at hxy
    rw [quadraticFactor_zero] at hxy
    simp only [smul_apply, smul_eq_mul] at hxy
    simp only [map_zero, zero_apply]
    linarith
  obtain ⟨v, hv⟩ : ∃ v : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      L.IsOrthoᵢ v := by
    have h := LinearMap.BilinForm.exists_orthogonal_basis hsymm
    have hfin : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by
      simp
    rw [hfin] at h
    exact h
  have hvnonzero := hv.not_isOrtho_basis_self_of_separatingLeft hsep
  let A : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ((LinearEquiv.finTwoArrow ℝ ℝ).symm.trans v.equivFun.symm).toContinuousLinearEquiv
  have hA (x : ℝ × ℝ) : A x = x.1 • v 0 + x.2 • v 1 := by
    simp [A, Basis.equivFun_symm_apply, Fin.sum_univ_two, LinearEquiv.finTwoArrow,
      finTwoArrowEquiv]
  let a : ℝ × ℝ → ℝ := fun x => B (A x) (v 0) (v 0)
  let b : ℝ × ℝ → ℝ := fun x => B (A x) (v 0) (v 1)
  let c : ℝ × ℝ → ℝ := fun x => B (A x) (v 1) (v 1)
  have hB : ContDiff ℝ ∞ (fun x => B (A x)) :=
    (contDiff_quadraticFactor hf).comp A.contDiff
  have ha : ContDiff ℝ ∞ a := (hB.clm_apply contDiff_const).clm_apply contDiff_const
  have hb : ContDiff ℝ ∞ b := (hB.clm_apply contDiff_const).clm_apply contDiff_const
  have hc : ContDiff ℝ ∞ c := (hB.clm_apply contDiff_const).clm_apply contDiff_const
  have ha0 : a 0 ≠ 0 := by simpa [a, L] using hvnonzero 0
  have hb0 : b 0 = 0 := by simpa [b, L] using hv (by decide : (0 : Fin 2) ≠ 1)
  have hc0 : c 0 ≠ 0 := by simpa [c, L] using hvnonzero 1
  have hd0 : c 0 - b 0 ^ 2 / a 0 ≠ 0 := by simpa [hb0] using hc0
  have hfA (x : ℝ × ℝ) : f (A x) = f 0 +
      (a x * x.1 ^ 2 + 2 * b x * x.1 * x.2 + c x * x.2 ^ 2) := by
    rw [eq_add_quadraticFactor_of_fderiv_eq_zero hf hcrit (A x)]
    congr 1
    change B (A x) (A x) (A x) = _
    conv_lhs => arg 2; rw [hA]
    conv_lhs => arg 1; arg 2; rw [hA]
    exact bilinear_apply_planar_expansion (B (A x)) (v 0) (v 1)
      (quadraticFactor_symmetric hf (A x) (v 0) (v 1)) x.1 x.2
  obtain ⟨e, s, t, hs, ht, he0, hezero, he, hei, hform⟩ :=
    exists_binary_quadratic_normalForm ha hb hc ha0 hd0
  let C : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans
      (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv
  have hC (x : EuclideanSpace ℝ (Fin 2)) : C x = (x 0, x 1) := rfl
  let q := (C.toHomeomorph.toOpenPartialHomeomorph.trans e).trans
    A.toHomeomorph.toOpenPartialHomeomorph
  have hq (x : EuclideanSpace ℝ (Fin 2)) : q x = A (e (C x)) := rfl
  have hqs : ∀ x ∈ q.source, C x ∈ e.source := fun x hx => hx.1.2
  refine ⟨q, ![s, t], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hs, ht]
  · exact ⟨⟨mem_univ _, by simpa using he0⟩, mem_univ _⟩
  · simp [hq, hezero]
  · exact A.contDiff.contDiffOn.comp
      (he.comp C.contDiff.contDiffOn (fun x hx => hqs x hx)) (fun _ _ => mem_univ _)
  · exact C.symm.contDiff.contDiffOn.comp
      (hei.comp A.symm.contDiff.contDiffOn (fun x hx => hx.2.1)) (fun _ _ => mem_univ _)
  · intro x hx
    rw [hq, hfA, hform (C x) (hqs x hx)]
    simp [Fin.sum_univ_two, hC]

end Poincare.Analysis.Calculus.Morse
