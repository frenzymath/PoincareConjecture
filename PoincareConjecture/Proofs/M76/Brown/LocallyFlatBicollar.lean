import PoincareConjecture.Proofs.M76.Brown.LocallyFlatSideCollars
import PoincareConjecture.Proofs.M76.Brown.TwoCollarGluing

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)

theorem exists_bicollar {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    ∃ O : Set V3, IsOpen O ∧ S ⊆ O ∧
      ∃ H : (S × Ioo (-1 : ℝ) 1) ≃ₜ O,
        ∀ s, (H (BrownCollar.bicollarBase s) : V3) = (s : V3) := by
  obtain ⟨C⟩ := hS.exists_ambient_side_collars
  exact ⟨C.collarUnion, C.isOpen_collarUnion,
    C.base_subset_positiveImage.trans subset_union_left,
    C.bicollarHomeomorph, C.bicollarHomeomorph_base⟩

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
