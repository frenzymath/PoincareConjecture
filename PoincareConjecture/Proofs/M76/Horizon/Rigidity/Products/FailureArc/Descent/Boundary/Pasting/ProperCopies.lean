import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.ResolutionCopies



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem AnnulusSquareCopies.proper_marked
    {X : Type*} [TopologicalSpace X] {f : Fin 2 → P2 → X} {g : P2 → X}
    (C : AnnulusSquareCopies f g) {R : Set X} (mark : Bool → Set X)
    (hin : ∀ j, MapsTo (f j) Sq R)
    (hfront : ∀ j (z : Sq), f j z ∈ frontier R ↔ (z : P2).2 = 0 ∨ (z : P2).2 = 1)
    (hbottom : ∀ j (t : I), f j (t, 0) ∈ mark false)
    (htop : ∀ j (t : I), f j (t, 1) ∈ mark true) :
    MapsTo g (squareAnnulus 8 1) R ∧
      (∀ z ∈ squareAnnulus 8 1,
        g z ∈ frontier R ↔ depth 8 z = -1 ∨ depth 8 z = 1) ∧
      (∀ z ∈ squareAnnulus 8 1, depth 8 z = -1 → g z ∈ mark false) ∧
      (∀ z ∈ squareAnnulus 8 1, depth 8 z = 1 → g z ∈ mark true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, z, rfl⟩ := C.exists_representation hx
    rw [C.val]
    exact hin j z.property
  · intro x hx
    obtain ⟨j, z, rfl⟩ := C.exists_representation hx
    rw [C.val, hfront, C.outer, C.inner]
  · intro x hx hdepth
    obtain ⟨j, z, rfl⟩ := C.exists_representation hx
    have hz := (C.outer j z).mp hdepth
    rw [C.val, show (z : P2) = (z.val.1, 0) from Prod.ext rfl hz]
    exact hbottom j ⟨z.val.1, z.property.1⟩
  · intro x hx hdepth
    obtain ⟨j, z, rfl⟩ := C.exists_representation hx
    have hz := (C.inner j z).mp hdepth
    rw [C.val, show (z : P2) = (z.val.1, 1) from Prod.ext rfl hz]
    exact htop j ⟨z.val.1, z.property.1⟩

end PoincareConjecture.M76.Dehn
