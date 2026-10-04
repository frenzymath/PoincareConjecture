import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.LocallyFlatBicollar
import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.BicollarSeparation

/-!
# Actual complementary components from the frozen locally flat sphere

All collar and separation data are produced from the literal original
parametrization and pointwise flattening charts. See Brown1960 Theorem0
for the source comparison and Brown derivation014, section5 for the
proved bicollared special case.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)

/-- The unchanged locally flat sphere input produces both actual
complementary components and both complete original ambient frontiers.
See Brown derivation014, section5. -/
theorem exists_complement_components {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    ∃ U V : Set V3, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Sᶜ ∧ frontier U = S ∧ frontier V = S ∧
      ∀ x ∈ Sᶜ, connectedComponentIn Sᶜ x = U ∨ connectedComponentIn Sᶜ x = V := by
  let : CompactSpace (sphere (0 : V3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V3) 1)
  let : CompactSpace S := hS.parametrization.compactSpace
  have hcompact : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  let : SimplyConnectedSpace S := hS.lifting_connectedness.1
  obtain ⟨C, hC, _, H, hbase⟩ := hS.exists_bicollar
  exact BrownCollar.exists_bicollar_complement_components hcompact.isClosed hC H hbase

end PoincareMT.M76.LocallyFlatTopologicalSphere
