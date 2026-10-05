import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Collars.PLDomainSideCollars
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Collars.SideCollarSigns

/-!
# The actual signed bicollar of a compact PL frontier

Both complete collars are produced from the original halfspace
charts, glued by the checked Brown construction, and retain the
whole base and original side. See Wall derivation006, sections3--4.
-/

set_option autoImplicit false

open Set BrownCollar

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- A nonempty compact frontier of an actual PL domain in a metric
ambient has a constructed signed bicollar fixing every original base
point. No collar or normal-orientation supplier is used.
See Brown1962 Theorems1/3 and Wall006, sections3--4. -/
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

end PoincareMT.M76
