import PoincareConjecture.Proofs.M38.Components









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38



theorem exists_component_decomposition (S : GeneralizedSliceCarrier.{u})
    (hS : IsCompact (Set.univ : Set S.carrier)) :
    ∃ n : ℕ, ∃ representative : Fin n → S.carrier,
      ∃ D : SmoothDisjointUnionData (fun i => componentCarrier S (representative i)) S,
        ∀ i, D.region i = connectedComponent (representative i) := by
  classical
  let : Finite (ConnectedComponents S.carrier) := finite_components S hS
  let : Fintype (ConnectedComponents S.carrier) := Fintype.ofFinite _
  let e := Fintype.equivFin (ConnectedComponents S.carrier)
  choose representative hrepresentative using
    (ConnectedComponents.surjective_coe :
      Function.Surjective (ConnectedComponents.mk : S.carrier → ConnectedComponents S.carrier))
  let r : Fin (Fintype.card (ConnectedComponents S.carrier)) → S.carrier :=
    fun i => representative (e.symm i)
  have hr (i) : ConnectedComponents.mk (r i) = e.symm i := hrepresentative (e.symm i)
  have hcover : (⋃ i, connectedComponent (r i)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    refine Set.mem_iUnion.mpr ⟨e (ConnectedComponents.mk x), ?_⟩
    have hclass : ConnectedComponents.mk (r (e (ConnectedComponents.mk x))) =
        ConnectedComponents.mk x := by
      rw [hr, e.symm_apply_apply]
    rw [ConnectedComponents.coe_eq_coe.mp hclass]
    exact mem_connectedComponent
  have hdisjoint : ∀ i j, i ≠ j →
      Disjoint (connectedComponent (r i)) (connectedComponent (r j)) := by
    intro i j hij
    apply connectedComponent_disjoint
    intro h
    have hclass := ConnectedComponents.coe_eq_coe.mpr h
    rw [hr, hr] at hclass
    exact hij (e.symm.injective hclass)
  let D : SmoothDisjointUnionData (fun i => componentCarrier S (r i)) S :=
    { region := fun i => connectedComponent (r i)
      region_open := fun i => (componentOpen S (r i)).isOpen
      region_closed := fun _ => isClosed_connectedComponent
      identify := fun i => componentRegionEquivalence S (r i)
      pairwise_disjoint := hdisjoint
      cover := hcover }
  exact ⟨_, r, D, fun _ => rfl⟩



theorem identity_conclusion (S : GeneralizedSliceCarrier.{u})
    (hS : IsCompact (Set.univ : Set S.carrier)) :
    Nonempty (SurgeryTopologyConclusion S S) := by
  obtain ⟨n, r, D, hregion⟩ := exists_component_decomposition S hS
  refine ⟨{
    piece_count := n
    piece := fun i => componentCarrier S (r i)
    piece_compact := fun i => componentCarrier_compact S hS (r i)
    piece_connected := fun i => componentCarrier_connected S (r i)
    kind := fun _ => .survivor
    survivor_region := D.region
    survivor := fun i _ => D.identify i
    survivor_component := fun i _ => ⟨r i, hregion i⟩
    survivor_cover := ?_
    survivor_disjoint := fun i j hij _ _ => D.pairwise_disjoint i j hij
    bundles := fun _ h => by cases h
    spaceforms := fun _ h => by cases h
    reconstruction := {
      initial := S
      disjoint_union := D
      operations := .refl } }⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ i, D.region i := by
    rw [D.cover]
    exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨i, rfl⟩, hi⟩

end PoincareConjecture.M38
