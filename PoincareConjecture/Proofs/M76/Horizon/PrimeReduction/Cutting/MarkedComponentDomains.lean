import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ClosedAttachmentComponentCarriers

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_marked_pl_component_domains
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {P : Set X}
    (hP : IsCompact P) (he : PLDomain e P)
    (B : κ → Set X) (hB : ∀ i, IsConnected (B i))
    (hBP : ∀ i, B i ⊆ frontier P) :
    Finite (ConnectedComponents P) ∧
      ∃ (D : ConnectedComponents P → Set X) (owner : κ → ConnectedComponents P),
        (∀ c, IsCompact (D c) ∧ PLDomain e (D c) ∧ IsConnected (D c) ∧
          D c ⊆ P ∧ frontier (D c) = D c ∩ frontier P) ∧
        Pairwise (fun c d => Disjoint (D c) (D d)) ∧ (⋃ c, D c) = P ∧
        (∀ i c, B i ⊆ D c ↔ owner i = c) ∧
        (∀ i c, owner i ≠ c → Disjoint (B i) (D c)) ∧
        (∀ x : P, D (ConnectedComponents.mk x) = connectedComponentIn P x) := by
  classical
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let : LocallyPathConnectedSpace P := he.locallyPathConnectedSpace
  choose a ha using (ConnectedComponents.surjective_coe :
    ∀ c : ConnectedComponents P, ∃ x : P, ConnectedComponents.mk x = c)
  let D : ConnectedComponents P → Set X := fun c => connectedComponentIn P (a c)
  have hmem (c : ConnectedComponents P) (x : P) :
      (x : X) ∈ D c ↔ ConnectedComponents.mk x = c := by
    change (x : X) ∈ connectedComponentIn P (a c) ↔ _
    rw [Topology.mem_componentIn_iff_component_class (a c).property x.property, ha]
  have hsub (c : ConnectedComponents P) : D c ⊆ P := connectedComponentIn_subset _ _
  have hpieces (c : ConnectedComponents P) :
      IsCompact (D c) ∧ PLDomain e (D c) ∧ IsConnected (D c) ∧
        D c ⊆ P ∧ frontier (D c) = D c ∩ frontier P := by
    have hc := isCompact_connectedComponentIn_of_mem hP (a c).property
    obtain ⟨U, hU, hDU⟩ := exists_open_inter_of_relative_open (hsub c)
      (isOpen_preimage_connectedComponentIn (a c).property)
    exact ⟨hc, he.connectedComponentIn hP (a c).property,
      isConnected_connectedComponentIn_iff.mpr (a c).property, hsub c,
      frontier_eq_inter_of_eq_inter_open hP.isClosed hc.isClosed hU hDU⟩
  have hdis : Pairwise fun c d => Disjoint (D c) (D d) := by
    intro c d hcd
    apply disjoint_left.mpr
    intro x hxc hxd
    exact hcd (((hmem c ⟨x, hsub c hxc⟩).mp hxc).symm.trans
      ((hmem d ⟨x, hsub c hxc⟩).mp hxd))
  have hcover : (⋃ c, D c) = P := by
    apply Subset.antisymm (iUnion_subset hsub)
    intro x hx
    exact mem_iUnion.mpr ⟨ConnectedComponents.mk (⟨x, hx⟩ : P),
      (hmem _ ⟨x, hx⟩).mpr rfl⟩
  choose b hb using fun i => (hB i).nonempty
  have hbP (i : κ) := hP.isClosed.frontier_subset (hBP i (hb i))
  let owner : κ → ConnectedComponents P := fun i => ConnectedComponents.mk ⟨b i, hbP i⟩
  have howned (i : κ) : B i ⊆ D (owner i) := by
    have hbD : b i ∈ D (owner i) := (hmem _ ⟨b i, hbP i⟩).mpr rfl
    have hwhole := (hB i).isPreconnected.subset_connectedComponentIn (hb i)
      ((hBP i).trans hP.isClosed.frontier_subset)
    change B i ⊆ connectedComponentIn P (a (owner i))
    rwa [connectedComponentIn_eq hbD]
  refine ⟨inferInstance, D, owner, hpieces, hdis, hcover, ?_, ?_, ?_⟩
  · intro i c
    constructor
    · intro h
      exact (hmem c ⟨b i, hbP i⟩).mp (h (hb i))
    · rintro rfl
      exact howned i
  · intro i c hic
    exact (hdis hic).mono_left (howned i)
  · intro x
    have hxD := (hmem (ConnectedComponents.mk x) x).mpr rfl
    exact connectedComponentIn_eq hxD

end PoincareConjecture.M76
