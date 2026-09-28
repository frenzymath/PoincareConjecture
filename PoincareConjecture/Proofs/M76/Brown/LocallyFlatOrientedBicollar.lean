import PoincareConjecture.Proofs.M76.Brown.LocallyFlatBoundedRegion
import PoincareConjecture.Proofs.M76.Brown.OrientedBicollar









set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)




theorem exists_bounded_oriented_bicollar {S : Set V3}
    (hS : LocallyFlatTopologicalSphere S) :
    ∃ U V O : Set V3, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = Sᶜ ∧
      frontier U = S ∧ frontier V = S ∧ IsCompact (closure U) ∧
      frontier (closure U) = S ∧ IsOpen O ∧ S ⊆ O ∧
      ∃ H : (S × Ioo (-1 : ℝ) 1) ≃ₜ O,
        (∀ s, (H (BrownCollar.bicollarBase s) : V3) = (s : V3)) ∧
        (∀ z, (z.2 : ℝ) < 0 → (H z : V3) ∈ U) ∧
        (∀ z, 0 < (z.2 : ℝ) → (H z : V3) ∈ V) := by
  let : CompactSpace (sphere (0 : V3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V3) 1)
  let : CompactSpace S := hS.parametrization.compactSpace
  let : SimplyConnectedSpace S := hS.lifting_connectedness.1
  have hcS : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨U, V, hU, hV, _, _, hdis, hunion, hfrontU, hfrontV, _, _,
      hcompact, hfront, hclass⟩ := hS.exists_bounded_complement_components
  obtain ⟨O, hO, hSO, H, hbase⟩ := hS.exists_bicollar
  obtain ⟨G, hGbase, hGneg, hGpos⟩ := BrownCollar.exists_bicollar_oriented_to_components
    hcS.isClosed hO H hbase hclass
  exact ⟨U, V, O, hU, hV, hdis, hunion, hfrontU, hfrontV, hcompact,
    hfront, hO, hSO, G, hGbase, hGneg, hGpos⟩

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
