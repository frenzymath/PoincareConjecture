import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.SelectedComponent
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.SourceDoubleComponents

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
  {S Q : Set E} {R : Set X}

instance (M : SourceDoubleComponents e f S Q R) : Finite M.Index := M.finite_components

def literalPartner (M : SourceDoubleComponents e f S Q R) :
    doubleLocusOn f S ≃ₜ doubleLocusOn f S :=
  (Homeomorph.setCongr M.space.symm).trans (M.partner.trans (Homeomorph.setCongr M.space))

theorem literalPartner_apply (M : SourceDoubleComponents e f S Q R)
    (x : doubleLocusOn f S) :
    (M.literalPartner x : E) = (M.partner ⟨x, M.space.symm.subset x.property⟩ : E) := rfl

theorem literalPartner_PL (M : SourceDoubleComponents e f S Q R) :
    M.literalPartner.IsFinitePL := M.partnerPL.setCongr M.space M.space

theorem literalPartner_involutive (M : SourceDoubleComponents e f S Q R) :
    Function.Involutive M.literalPartner := by
  intro x
  apply Subtype.ext
  exact congrArg (fun y : M.graph.space => (y : E))
    (M.involutive ⟨x, M.space.symm.subset x.property⟩)

theorem literalPartner_value (M : SourceDoubleComponents e f S Q R)
    (x : doubleLocusOn f S) : f x = f (M.literalPartner x) :=
  (M.value ⟨x, M.space.symm.subset x.property⟩).symm

theorem literalPartner_free (M : SourceDoubleComponents e f S Q R)
    (x : doubleLocusOn f S) : (x : E) ≠ M.literalPartner x :=
  (M.free ⟨x, M.space.symm.subset x.property⟩).symm

theorem literalPartner_unique (M : SourceDoubleComponents e f S Q R)
    (x : doubleLocusOn f S) (y : E) (hy : y ∈ S)
    (hval : f x = f y) (hne : (x : E) ≠ y) :
    y = (M.literalPartner x : E) :=
  M.unique ⟨x, M.space.symm.subset x.property⟩ y hy hne hval

theorem literalPartner_component (M : SourceDoubleComponents e f S Q R)
    (i : M.Index) (x : doubleLocusOn f S) (hx : (x : E) ∈ M.pieces i) :
    (M.literalPartner x : E) ∈ M.pieces (M.mate i) :=
  (M.partner_component i ⟨x, M.space.symm.subset x.property⟩).mp hx

end PoincareConjecture.M76.Dehn.Annuli.SourceDoubleComponents
