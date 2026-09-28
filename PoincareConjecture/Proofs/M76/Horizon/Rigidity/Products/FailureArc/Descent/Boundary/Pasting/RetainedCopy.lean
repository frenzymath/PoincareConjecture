import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.SourceCopies
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.AnnulusSquareCopies

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

variable {X : Type*} {f : Fin 2 → P2 → X} {g : P2 → X}

def retainedDiskCopy (C : AnnulusSquareCopies f g) {E : Set P2} (H : Sq ≃ₜ E) : E → P2 :=
  fun x ↦ C.chart 0 (H.symm x)

theorem retainedDiskCopy_injective (C : AnnulusSquareCopies f g) {E : Set P2} (H : Sq ≃ₜ E) :
    Function.Injective (C.retainedDiskCopy H) := by
  intro x y h
  exact H.symm.injective ((C.chart 0).injective (Subtype.ext h))

theorem retainedDiskCopy_continuous (C : AnnulusSquareCopies f g) {E : Set P2} (H : Sq ≃ₜ E) :
    Continuous (C.retainedDiskCopy H) :=
  continuous_subtype_val.comp ((C.chart 0).continuous.comp H.symm.continuous)

theorem double_locus_eq_original_retained
    (C : AnnulusSquareCopies f g) {E : Set P2} (H : Sq ≃ₜ E) (old : P2 → X)
    (hdouble : {x : P2 | x ∈ squareAnnulus 8 1 ∧
        ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g y = g x} =
      (fun z : Sq ↦ (C.chart 0 z : P2)) ''
        {u : Sq | ∃ v : Sq, v ≠ u ∧ old (H v) = old (H u)}) :
    doubleLocusOn g (squareAnnulus 8 1) =
      C.retainedDiskCopy H '' {x : E | ∃ y : E, old x = old y ∧ (x : P2) ≠ y} := by
  have hrewrite : doubleLocusOn g (squareAnnulus 8 1) =
      {x : P2 | x ∈ squareAnnulus 8 1 ∧ ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g y = g x} := by
    ext x
    simp only [doubleLocusOn, mem_ofPred_eq]
    constructor
    · rintro ⟨hx, y, hy, hval, hne⟩
      exact ⟨hx, y, hy, hne.symm, hval.symm⟩
    · rintro ⟨hx, y, hy, hne, hval⟩
      exact ⟨hx, y, hy, hval.symm, hne.symm⟩
  rw [hrewrite, hdouble]
  apply Subset.antisymm
  · rintro x ⟨u, ⟨v, hv, he⟩, rfl⟩
    refine ⟨H u, ⟨H v, he.symm, ?_⟩, ?_⟩
    · intro huv
      exact hv (H.injective (Subtype.ext huv)).symm
    · simp only [retainedDiskCopy, Homeomorph.symm_apply_apply]
  · rintro x ⟨u, ⟨v, he, hne⟩, rfl⟩
    refine ⟨H.symm u, ⟨H.symm v, ?_, ?_⟩, rfl⟩
    · intro hvu
      exact hne (congrArg Subtype.val (H.symm.injective hvu).symm)
    · simpa only [Homeomorph.apply_symm_apply] using he.symm

theorem retainedDiskCopy_boundary_iff
    (C : AnnulusSquareCopies f g) {E Q₀ Q₁ : Set P2} (H : Sq ≃ₜ E)
    (houter : ∀ z : Sq, (H z : P2) ∈ Q₀ ↔ (z : P2).2 = 0)
    (hinner : ∀ z : Sq, (H z : P2) ∈ Q₁ ↔ (z : P2).2 = 1) (x : E) :
    (depth 8 (C.retainedDiskCopy H x) = -1 ∨ depth 8 (C.retainedDiskCopy H x) = 1) ↔
      (x : P2) ∈ Q₀ ∪ Q₁ := by
  change (depth 8 (C.chart 0 (H.symm x) : P2) = -1 ∨
    depth 8 (C.chart 0 (H.symm x) : P2) = 1) ↔ _
  rw [C.outer, C.inner, ← houter, ← hinner, Homeomorph.apply_symm_apply, mem_union]

end PoincareConjecture.M76.Dehn.AnnulusSquareCopies
