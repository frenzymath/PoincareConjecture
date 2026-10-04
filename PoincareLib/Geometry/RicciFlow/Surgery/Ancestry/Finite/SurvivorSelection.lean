import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Finite.PointGroups

/-!
# Selecting the actual survivor containing a point

The finite survivor cover identifies each post-point's entire connected
component, as in MT Proposition 15.3, printed pp. 357--358.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT

/-- Select a survivor whose region is exactly the point's component
(MT Proposition 15.3, pp. 357--358). -/
noncomputable def m56SurvivorSelection {A B : GeneralizedSliceCarrier.{u}}
    (C : SurgeryTopologyConclusion A B) (x : B.carrier) :
    {i : Fin C.piece_count // C.kind i = .survivor ∧
      C.survivor_region i = connectedComponent x} := by
  classical
  have hex : ∃ i : Fin C.piece_count, C.kind i = .survivor ∧
      C.survivor_region i = connectedComponent x := by
    have hx : x ∈ ⋃ i : {i // C.kind i = .survivor}, C.survivor_region i.1 := by
      rw [C.survivor_cover]
      exact mem_univ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨z, hz⟩ := C.survivor_component i.1 i.2
    refine ⟨i.1, i.2, ?_⟩
    rw [hz] at hi ⊢
    exact connectedComponent_eq hi
  exact ⟨hex.choose, hex.choose_spec⟩

end PoincareMT
