import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.AmbientSideCollars
import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Coordinates.LocallyFlatNormalAtlas

/-!
# Actual side collars from the frozen pointwise-flat sphere

Only the original parametrization and flattening fields are consumed.
The normal section, side regions and full collars are all constructed.
See Brown derivation013, sections1--5. Bicollar gluing and Schoenflies
remain subsequent proof obligations.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)

/-- The frozen pointwise-flat sphere produces both actual full side
collars, retaining their common ambient neighborhood and every original
base value. See Brown derivations012--013. -/
theorem exists_ambient_side_collars {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    Nonempty (BrownCollar.AmbientSideCollars S) := by
  let : CompactSpace (sphere (0 : V3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V3) 1)
  let : CompactSpace S := hS.parametrization.compactSpace
  have hcompact : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨x0, hx0⟩ :=
    (show (sphere (0 : V3) 1).Nonempty from NormedSpace.sphere_nonempty.mpr zero_le_one)
  let : Nonempty S := ⟨hS.parametrization ⟨x0, hx0⟩⟩
  obtain ⟨a, ha, hcompat⟩ := hS.exists_coherent_normal_units
  obtain ⟨E, hcover, hpair, hgerm⟩ :=
    hS.flatteningAtlas.exists_oriented_charts a ha hcompat
  exact BrownCollar.exists_ambient_side_collars hcompact E hcover hpair hgerm

end PoincareMT.M76.LocallyFlatTopologicalSphere
