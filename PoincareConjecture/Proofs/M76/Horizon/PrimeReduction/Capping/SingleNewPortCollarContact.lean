import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SingleNewPortFilling

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.single_new_port_filling_collar_contact
    {X F α κ : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R C : Set X}
    (c : MarkedSphereCut e R κ) (d : MarkedSphereCut e R (Option κ))
    (hCd : C ⊆ d.carrier)
    (hinside : closure (d.collar none) ⊆ interior c.carrier)
    (side : Bool) (hchosen : d.ports (none,side) ⊆ C)
    (hopposite : Disjoint (d.ports (none,!side)) C)
    (phi : X → F) (hphii : InjOn phi c.carrier) (hCc : C ⊆ c.carrier)
    (caps : κ × Bool → Set F)
    (hcontact : ∀ j, caps j ∩ phi '' c.carrier = phi '' c.ports j) :
    (phi '' C ∪ ⋃ j : {j : κ × Bool // c.ports j ⊆ C}, caps j) ∩
        phi '' closure (d.collar none) = phi '' d.ports (none,side) := by
  have hclosed : closure (d.collar none) ⊆ c.carrier := hinside.trans interior_subset
  have hportNew : d.ports (none,side) ⊆ closure (d.collar none) := d.portClosure _
  have hcapDis (j : κ × Bool) : Disjoint (caps j) (phi '' closure (d.collar none)) := by
    apply disjoint_left.mpr
    rintro y hy ⟨z,hz,rfl⟩
    obtain ⟨w,hw,hwz⟩ := (hcontact j).subset ⟨hy,⟨z,hclosed hz,rfl⟩⟩
    have hwfront : w ∈ frontier c.carrier := by
      apply c.frontierCut.symm.subset
      exact Or.inr (mem_iUnion.mpr ⟨j,hw⟩)
    have hwc : w ∈ c.carrier := c.plCut.closed.frontier_subset hwfront
    have hweq : w = z := hphii hwc (hclosed hz) hwz
    exact hwfront.2 (hweq.symm ▸ hinside hz)
  have hphysical : C ∩ closure (d.collar none) = d.ports (none,side) := by
    apply Subset.antisymm
    · intro z hz
      have h := (d.collarContact none).subset ⟨hz.2,hCd hz.1⟩
      cases side
      · exact h.resolve_right (fun ht => disjoint_left.mp hopposite ht hz.1)
      · exact h.resolve_left (fun hf => disjoint_left.mp hopposite hf hz.1)
    · exact fun z hz => ⟨hchosen hz,hportNew hz⟩
  apply Subset.antisymm
  · rintro y ⟨hyC | hyCaps,hyN⟩
    · obtain ⟨z,hz,rfl⟩ := hyC
      obtain ⟨w,hw,hwz⟩ := hyN
      have hwz' := hphii (hclosed hw) (hCc hz) hwz
      exact ⟨z,hphysical.subset ⟨hz,hwz' ▸ hw⟩,rfl⟩
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hyCaps
      exact False.elim (disjoint_left.mp (hcapDis j) hj hyN)
  · rintro y ⟨z,hz,rfl⟩
    exact ⟨Or.inl ⟨z,hchosen hz,rfl⟩,⟨z,hportNew hz,rfl⟩⟩

end PoincareConjecture.M76
