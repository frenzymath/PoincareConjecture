import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.LocallyFlatSideCollars
import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.TwoCollarGluing

/-!
# An actual bicollar from the frozen pointwise-flat sphere

The normal section, actual side regions, both local and full collars,
and the signed gluing are constructed from the original sphere data.
See Brown1962 Theorem3 and Brown derivations010--015. The separate
Schoenflies and full ball-pair recognition arguments remain open.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)

/-- Pointwise local flatness of the literal original sphere produces
an actual ambient-open bicollar fixing every original base point.
No global collar or side-existence assumption is consumed.
See Brown1962 Theorem3 and Brown derivations010--015. -/
theorem exists_bicollar {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    ∃ O : Set V3, IsOpen O ∧ S ⊆ O ∧
      ∃ H : (S × Ioo (-1 : ℝ) 1) ≃ₜ O,
        ∀ s, (H (BrownCollar.bicollarBase s) : V3) = (s : V3) := by
  obtain ⟨C⟩ := hS.exists_ambient_side_collars
  exact ⟨C.collarUnion, C.isOpen_collarUnion,
    C.base_subset_positiveImage.trans subset_union_left,
    C.bicollarHomeomorph, C.bicollarHomeomorph_base⟩

end PoincareMT.M76.LocallyFlatTopologicalSphere
