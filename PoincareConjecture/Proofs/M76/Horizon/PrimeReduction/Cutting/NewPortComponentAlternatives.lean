import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedExtensionPorts









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.restored_component_of_new_port
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (c : MarkedSphereCut e R κ) (d : MarkedSphereCut e R (Option κ))
    (hcut : d.carrier = c.carrier \ d.collar none)
    (hinside : closure (d.collar none) ⊆ interior c.carrier)
    {x : X} (_hx : x ∈ d.carrier) (side : Bool)
    (hport : d.ports (none,side) ⊆ connectedComponentIn d.carrier x) :
    ∃ y : X, y ∈ d.ports (none,!side) ∧
      connectedComponentIn c.carrier x =
        (connectedComponentIn d.carrier x ∪ connectedComponentIn d.carrier y) ∪
          closure (d.collar none) ∧
      ((d.ports (none,!side) ⊆ connectedComponentIn d.carrier x ∧
        connectedComponentIn c.carrier x =
          connectedComponentIn d.carrier x ∪ closure (d.collar none)) ∨
       (Disjoint (d.ports (none,!side)) (connectedComponentIn d.carrier x) ∧
        Disjoint (connectedComponentIn d.carrier y) (connectedComponentIn d.carrier x))) := by
  classical
  let : LocallyPathConnectedSpace d.carrier := d.plCut.locallyPathConnectedSpace
  have hrestore : d.carrier ∪ closure (d.collar none) = c.carrier := by
    apply Subset.antisymm
    · exact union_subset (hcut.subset.trans sdiff_subset) (hinside.trans interior_subset)
    · intro z hz
      by_cases hn : z ∈ d.collar none
      · exact Or.inr (subset_closure hn)
      · exact Or.inl (hcut.symm.subset ⟨hz,hn⟩)
  have hcollar : IsConnected (closure (d.collar none)) := by
    let : ConnectedSpace (d.spheres none) :=
      isConnected_iff_connectedSpace.mp (d.spherePL none).compact_connected.2
    let : ConnectedSpace (closure (d.collar none)) :=
      (d.product none).connectedSpace_iff.mp inferInstance
    exact isConnected_iff_connectedSpace.mpr inferInstance
  have hp (j : Bool) : IsConnected (d.ports (none,j)) :=
    (d.portPL (none,j)).compact_connected.2
  have hcontact : d.carrier ∩ closure (d.collar none) =
      d.ports (none,side) ∪ d.ports (none,!side) := by
    rw [inter_comm]
    change closure (d.collar none) ∩ (R \ ⋃ j, d.collar j) = _
    rw [d.collarContact]
    cases side
    · rfl
    · exact union_comm _ _
  have hportCut (j : Bool) : d.ports (none,j) ⊆ d.carrier := by
    intro z hz
    apply ((d.collarContact none).symm.subset _).2
    cases j
    · exact Or.inl hz
    · exact Or.inr hz
  obtain ⟨a,ha⟩ := (hp side).nonempty
  obtain ⟨y,hy⟩ := (hp (!side)).nonempty
  have haC := hport ha
  have haOld := connectedComponentIn_mono x (hcut.subset.trans sdiff_subset) haC
  have hformula := (Topology.componentIn_closed_attachment_of_two_connected_ports
    (P := d.carrier) d.plCut.closed isClosed_closure hcollar
    (hp side) (hp (!side)) hcontact ha hy).1
  rw [hrestore,← connectedComponentIn_eq haC,← connectedComponentIn_eq haOld] at hformula
  have hother : d.ports (none,!side) ⊆ connectedComponentIn d.carrier y :=
    (hp (!side)).isPreconnected.subset_connectedComponentIn hy (hportCut (!side))
  refine ⟨y,hy,hformula,?_⟩
  by_cases hyC : y ∈ connectedComponentIn d.carrier x
  · left
    have heq := connectedComponentIn_eq hyC
    refine ⟨heq.symm ▸ hother, ?_⟩
    simpa only [← heq,union_self] using hformula
  · right
    have hdis : Disjoint (connectedComponentIn d.carrier y)
        (connectedComponentIn d.carrier x) := by
      apply disjoint_left.mpr
      intro z hzy hzx
      have heq := (connectedComponentIn_eq hzy).trans (connectedComponentIn_eq hzx).symm
      exact hyC (heq ▸ mem_connectedComponentIn (hportCut (!side) hy))
    exact ⟨hdis.mono_left hother,hdis⟩

end PoincareConjecture.M76
