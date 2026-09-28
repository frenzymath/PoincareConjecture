import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Set.Card










set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.Dehn


theorem isClopen_of_finite_disjoint_closed_cover
    {X I : Type*} [TopologicalSpace X] [Finite I] (U : I → Set X)
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hcover : ⋃ i, U i = univ) (i : I) : IsClopen (U i) := by
  refine ⟨hclosed i, ?_⟩
  rw [← isClosed_compl_iff, compl_eq_univ_sdiff, ← hcover, iUnion_sdiff]
  apply isClosed_iUnion_of_finite
  intro j
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simpa only [(hdisj hji).sdiff_eq_left] using hclosed j



theorem exists_connected_components_equiv_of_finite_closed_partition
    {X I : Type*} [TopologicalSpace X] [Finite I] (U : I → Set X)
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hcover : ⋃ i, U i = univ) (hconn : ∀ i, IsConnected (U i)) :
    ∃ e : ConnectedComponents X ≃ I,
      ∀ (x : X) (i : I), e (ConnectedComponents.mk x) = i ↔ x ∈ U i := by
  let hc := isClopen_of_finite_disjoint_closed_cover U hclosed hdisj hcover
  let e := ConnectedComponents.equivOfIsClopenOfIsConnected hc hdisj hcover hconn
  refine ⟨e, ?_⟩
  intro x i
  constructor
  · intro h
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hcover x
    have hj' : e (ConnectedComponents.mk x) = j :=
      ConnectedComponents.equivOfIsClopenOfIsConnected_mk hc hdisj hcover hconn x hj
    exact (hj'.symm.trans h) ▸ hj
  · intro hx
    exact ConnectedComponents.equivOfIsClopenOfIsConnected_mk hc hdisj hcover hconn x hx



theorem connected_components_mark_counts_of_finite_closed_partition
    {X I : Type*} [TopologicalSpace X] [Finite I] (U : I → Set X)
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hcover : ⋃ i, U i = univ) (hconn : ∀ i, IsConnected (U i)) (Q : Set X) :
    (ConnectedComponents.mk '' Q).ncard = {i | (U i ∩ Q).Nonempty}.ncard ∧
      (ConnectedComponents.mk '' Q)ᶜ.ncard = {i | Disjoint (U i) Q}.ncard := by
  obtain ⟨e, he⟩ := exists_connected_components_equiv_of_finite_closed_partition
    U hclosed hdisj hcover hconn
  have himage : e '' (ConnectedComponents.mk '' Q) = {i | (U i ∩ Q).Nonempty} := by
    ext i
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hi⟩
      exact ⟨x, (he x i).mp hi, hx⟩
    · rintro ⟨x, hxU, hxQ⟩
      exact ⟨ConnectedComponents.mk x, ⟨x, hxQ, rfl⟩, (he x i).mpr hxU⟩
  constructor
  · rw [← himage, Set.ncard_image_of_injective _ e.injective]
  · have hcompl : e '' (ConnectedComponents.mk '' Q)ᶜ = {i | Disjoint (U i) Q} := by
      rw [e.image_compl, himage]
      ext i
      simp only [mem_compl_iff, mem_ofPred_eq, Set.not_nonempty_iff_eq_empty,
        disjoint_iff_inter_eq_empty]
    rw [← hcompl, Set.ncard_image_of_injective _ e.injective]



theorem connected_components_mark_counts_of_ambient_partition
    {X I : Type*} [TopologicalSpace X] [Finite I] {S : Set X} (U : I → Set X)
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hcover : ⋃ i, U i = S) (hconn : ∀ i, IsConnected (U i)) (Q : Set X) :
    (ConnectedComponents.mk '' ((Subtype.val : S → X) ⁻¹' Q)).ncard =
        {i | (U i ∩ Q).Nonempty}.ncard ∧
      (ConnectedComponents.mk '' ((Subtype.val : S → X) ⁻¹' Q))ᶜ.ncard =
        {i | Disjoint (U i) Q}.ncard := by
  let V (i : I) : Set S := (Subtype.val : S → X) ⁻¹' U i
  have hsub (i : I) : U i ⊆ S := by
    rw [← hcover]
    exact subset_iUnion U i
  have hvcover : ⋃ i, V i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    change ∃ i, (x : X) ∈ U i
    exact mem_iUnion.mp (hcover.symm ▸ x.property)
  have hvconn (i : I) : IsConnected (V i) := by
    let : ConnectedSpace (U i) := isConnected_iff_connectedSpace.mp (hconn i)
    let c : U i → S := fun x ↦ ⟨x, hsub i x.property⟩
    have hc : Continuous c := continuous_subtype_val.subtype_mk _
    have hr : range c = V i := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    exact hr ▸ isConnected_range hc
  have hvdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)) :=
    fun i j hij ↦ (hdisj hij).preimage _
  have h := connected_components_mark_counts_of_finite_closed_partition V
    (fun i ↦ (hclosed i).preimage continuous_subtype_val) hvdisj hvcover hvconn
    ((Subtype.val : S → X) ⁻¹' Q)
  have hmeet (i : I) :
      (V i ∩ ((Subtype.val : S → X) ⁻¹' Q)).Nonempty ↔ (U i ∩ Q).Nonempty := by
    constructor
    · rintro ⟨x, hx, hq⟩
      exact ⟨x, hx, hq⟩
    · rintro ⟨x, hx, hq⟩
      exact ⟨⟨x, hsub i hx⟩, hx, hq⟩
  have havoid (i : I) :
      Disjoint (V i) ((Subtype.val : S → X) ⁻¹' Q) ↔ Disjoint (U i) Q := by
    rw [disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty,
      ← not_nonempty_iff_eq_empty, ← not_nonempty_iff_eq_empty, hmeet]
  simpa only [hmeet, havoid] using h

end PoincareConjecture.M76.Dehn
