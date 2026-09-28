import PoincareConjecture.Proofs.M76.Brown.AmbientSideCollars
import PoincareConjecture.Proofs.M76.Brown.LocallyFlatNormalAtlas










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)




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

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
