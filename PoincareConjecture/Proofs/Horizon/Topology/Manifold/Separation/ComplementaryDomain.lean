import Mathlib.Topology.Clopen
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

theorem complementary_domain [T2Space X] {Y K : Set X}
    (hY : IsClopen Y) (hYcompact : IsCompact Y)
    (hK : IsCompact K) (hKY : K ⊆ Y)
    (hregular : closure (interior K) = K) :
    IsCompact (Y \ interior K) ∧
      interior (Y \ interior K) = Y \ K ∧
      closure (interior (Y \ interior K)) = Y \ interior K ∧
      frontier (Y \ interior K) = frontier K := by
  have hL : IsCompact (Y \ interior K) := hYcompact.diff isOpen_interior
  have hLi : interior (Y \ interior K) = Y \ K := by
    rw [sdiff_eq, interior_inter, hY.isOpen.interior_eq, interior_compl, hregular]
    rfl
  have hclosure : closure (Y \ K) = Y \ interior K := by
    have hinter : closure (Y ∩ Kᶜ) = Y ∩ closure Kᶜ := by
      apply Subset.antisymm
      · simpa only [hY.isClosed.closure_eq] using
          (closure_inter_subset (s := Y) (t := Kᶜ))
      · exact hY.isOpen.inter_closure
    simpa only [sdiff_eq, closure_compl] using hinter
  refine ⟨hL, hLi, by rw [hLi, hclosure], ?_⟩
  rw [hL.isClosed.frontier_eq, hLi, hK.isClosed.frontier_eq]
  ext x
  constructor
  · rintro ⟨⟨hxY, hxi⟩, hx⟩
    refine ⟨?_, hxi⟩
    by_contra hxK
    exact hx ⟨hxY, hxK⟩
  · rintro ⟨hxK, hxi⟩
    exact ⟨⟨hKY hxK, hxi⟩, fun hx => hx.2 hxK⟩

theorem complementary_domain_subset {Y K D : Set X}
    (henclose : Y \ D ⊆ interior K) : Y \ interior K ⊆ D := by
  intro x hx
  by_contra hxD
  exact hx.2 (henclose ⟨hx.1, hxD⟩)

end Poincare.Topology
