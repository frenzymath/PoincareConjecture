import PoincareConjecture.Proofs.M76.Wall.PLDomainSideCollars
import PoincareConjecture.Proofs.M76.Wall.SideCollarSigns









set_option autoImplicit false

open Set BrownCollar

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem PLDomain.exists_compact_frontier_bicollar
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {P : Set X}
    (hP : PLDomain e P) (hF : IsCompact (frontier P))
    (hne : (frontier P).Nonempty) :
    ∃ U : Set X, IsOpen U ∧ frontier P ⊆ U ∧
      ∃ H : (frontier P × Ioo (-1 : ℝ) 1) ≃ₜ U,
        (∀ x, (H (bicollarBase x) : X) = (x : X)) ∧
        (∀ z, (H z : X) ∈ P ↔ 0 ≤ (z.2 : ℝ)) ∧
        ∀ z, (H z : X) ∈ frontier P ↔ (z.2 : ℝ) = 0 := by
  obtain ⟨C, hpositive, _⟩ := hP.exists_side_collars hF hne
  refine ⟨C.collarUnion, C.isOpen_collarUnion,
    C.base_subset_positiveImage.trans subset_union_left,
    C.bicollarHomeomorph, C.bicollarHomeomorph_base, ?_, C.bicollar_mem_base_iff⟩
  intro z
  simpa only [hpositive] using C.bicollar_mem_positive_iff z

end PoincareConjecture.M76
