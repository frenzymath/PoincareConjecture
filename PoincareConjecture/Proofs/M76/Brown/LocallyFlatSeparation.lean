import PoincareConjecture.Proofs.M76.Brown.LocallyFlatBicollar
import PoincareConjecture.Proofs.M76.Brown.BicollarSeparation










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)




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

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
