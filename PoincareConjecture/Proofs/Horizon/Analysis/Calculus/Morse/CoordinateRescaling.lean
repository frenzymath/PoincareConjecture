import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SquareCompletion
import Mathlib.Topology.OpenPartialHomeomorph.Composition

noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff

namespace Poincare.Analysis.Calculus.Morse

private abbrev E2 := EuclideanSpace Real (Fin 2)

theorem exists_diagonal_rescaling_localInverse
    {u w : E2 → Real} {U : Set E2} (hU : IsOpen U) (h0 : 0 ∈ U)
    (hu : ContDiffOn Real ∞ u U) (hw : ContDiffOn Real ∞ w U)
    (hu0 : u 0 ≠ 0) (hw0 : w 0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph E2 E2,
      0 ∈ e.source ∧ e 0 = 0 ∧ MapsTo e e.source U ∧
      ContDiffOn Real ∞ e e.source ∧ ContDiffOn Real ∞ e.symm e.target ∧
      ∀ x ∈ e.source, u (e x) * e x 0 = x 0 ∧ w (e x) * e x 1 = x 1 := by
  let C : E2 ≃L[Real] Real × Real :=
    (EuclideanSpace.equiv (Fin 2) Real).trans
      (LinearEquiv.finTwoArrow Real Real).toContinuousLinearEquiv
  have hC (x : E2) : C x = (x 0, x 1) := rfl
  have hC0 (x : Real × Real) : C.symm x 0 = x.1 := rfl
  have hC1 (x : Real × Real) : C.symm x 1 = x.2 := rfl
  let V := C.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage C.symm.continuous
  have h0V : (0 : Real × Real) ∈ V := by simpa [V] using h0
  have huV : ContDiffOn Real ∞ (u ∘ C.symm) V :=
    hu.comp C.symm.contDiff.contDiffOn (fun _ hx => hx)
  have hwV : ContDiffOn Real ∞ (w ∘ C.symm) V :=
    hw.comp C.symm.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨Q, hQ0, hQzero, hQV, hQcoe, hQ, hQi⟩ :=
    exists_rescalingShear_localInverse hV h0V huV (contDiffOn_const (c := (0 : Real))) hwV
      (by simpa using hu0) (by simpa using hw0)
  have h0t : (0 : Real × Real) ∈ Q.target := hQzero ▸ Q.map_source hQ0
  have hQi0 : Q.symm 0 = 0 := by
    calc
      Q.symm 0 = Q.symm (Q 0) := by rw [hQzero]
      _ = 0 := Q.left_inv hQ0
  let e := (C.toHomeomorph.toOpenPartialHomeomorph.trans Q.symm).trans
    C.symm.toHomeomorph.toOpenPartialHomeomorph
  have he (x : E2) : e x = C.symm (Q.symm (C x)) := rfl
  have hei (x : E2) : e.symm x = C.symm (Q (C x)) := rfl
  have hes : ∀ x ∈ e.source, C x ∈ Q.target := fun _ hx => hx.1.2
  have het : ∀ x ∈ e.target, C x ∈ Q.source := fun _ hx => hx.2.1
  refine ⟨e, ⟨⟨mem_univ _, by simpa using h0t⟩, mem_univ _⟩,
    by simp [he, hQi0], (fun x hx => hQV (Q.map_target (hes x hx))), ?_, ?_, ?_⟩
  · exact C.symm.contDiff.contDiffOn.comp
      (hQi.comp C.contDiff.contDiffOn (fun x hx => hes x hx)) (fun _ _ => mem_univ _)
  · exact C.symm.contDiff.contDiffOn.comp
      (hQ.comp C.contDiff.contDiffOn (fun x hx => het x hx)) (fun _ _ => mem_univ _)
  · intro x hx
    have h := Q.right_inv (hes x hx)
    rw [hQcoe] at h
    constructor
    · simpa [hC, he, hC0, rescalingShearMap] using congrArg Prod.fst h
    · simpa [hC, he, hC1, rescalingShearMap] using congrArg Prod.snd h

end Poincare.Analysis.Calculus.Morse
