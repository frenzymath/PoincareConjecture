import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortComponentCarriers
import PoincareConjecture.Proofs.M76.Wall.PLDomainLocalPathConnected
import PoincareConjecture.Proofs.M76.Wall.SphericalFrontierFilling








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.exists_new_port_subset_of_punctured_component
    {X E ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R : Set X}
    (c : MarkedSphereCut e R κ) (d : MarkedSphereCut e R (Option κ))
    (hcut : d.carrier = c.carrier \ d.collar none)
    (hinside : closure (d.collar none) ⊆ interior c.carrier)
    (hno : HasNoPuncturedSphereComponents e f c.carrier)
    {x : X} (hx : x ∈ d.carrier)
    (hmodel : HasPuncturedSphereModel e f (connectedComponentIn d.carrier x)) :
    ∃ b : Bool, d.ports (none, b) ⊆ connectedComponentIn d.carrier x := by
  classical
  let : LocallyPathConnectedSpace d.carrier := d.plCut.locallyPathConnectedSpace
  have hrestore : d.carrier ∪ closure (d.collar none) = c.carrier := by
    apply Subset.antisymm
    · exact union_subset (hcut.subset.trans sdiff_subset) (hinside.trans interior_subset)
    · intro y hy
      by_cases hyN : y ∈ d.collar none
      · exact Or.inr (subset_closure hyN)
      · exact Or.inl (hcut.symm.subset ⟨hy, hyN⟩)
  have hcollar : IsConnected (closure (d.collar none)) := by
    let : ConnectedSpace (d.spheres none) :=
      isConnected_iff_connectedSpace.mp (d.spherePL none).compact_connected.2
    let : ConnectedSpace (closure (d.collar none)) :=
      (d.product none).connectedSpace_iff.mp inferInstance
    exact isConnected_iff_connectedSpace.mpr inferInstance
  have hport (b : Bool) : IsConnected (d.ports (none, b)) :=
    (d.portPL (none, b)).compact_connected.2
  have hcontact : d.carrier ∩ closure (d.collar none) =
      d.ports (none, false) ∪ d.ports (none, true) := by
    rw [inter_comm]
    exact d.collarContact none
  have hportCut (b : Bool) : d.ports (none, b) ⊆ d.carrier := by
    intro y hy
    apply (hcontact.symm.subset _).1
    cases b
    · exact Or.inl hy
    · exact Or.inr hy
  obtain ⟨a, ha⟩ := (hport false).nonempty
  obtain ⟨b, hb⟩ := (hport true).nonempty
  have hportA : d.ports (none, false) ⊆ connectedComponentIn d.carrier a :=
    (hport false).isPreconnected.subset_connectedComponentIn ha (hportCut false)
  have hportB : d.ports (none, true) ⊆ connectedComponentIn d.carrier b :=
    (hport true).isPreconnected.subset_connectedComponentIn hb (hportCut true)
  by_contra hmissing
  have hmiss : x ∉ connectedComponentIn d.carrier a ∪ connectedComponentIn d.carrier b := by
    rintro (hxa | hxb)
    · apply hmissing
      refine ⟨false, ?_⟩
      rw [← connectedComponentIn_eq hxa]
      exact hportA
    · apply hmissing
      refine ⟨true, ?_⟩
      rw [← connectedComponentIn_eq hxb]
      exact hportB
  have hcomponents := Topology.componentIn_closed_attachment_of_two_connected_ports
    (P := d.carrier) d.plCut.closed isClosed_closure hcollar
    (hport false) (hport true) hcontact ha hb
  have heq : connectedComponentIn c.carrier x = connectedComponentIn d.carrier x := by
    rw [← hrestore]
    exact hcomponents.2 x hx hmiss
  exact hno x ((hcut.subset hx).1) (heq.symm ▸ hmodel)

end PoincareConjecture.M76
