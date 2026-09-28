import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPairs
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedImages










set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.Dehn


theorem retained_double_component_counts
    {E Y X I : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace Y] [T2Space Y] [Finite I]
    {S G K Q : Set E} {G' Q' : Set Y} {f : E → X}
    (U : I → Set E) (mate : I → I) (partner : G → G)
    (hG : G = {x | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y})
    (hcover : ⋃ i, U i = G)
    (hcompact : ∀ i, IsCompact (U i)) (hconn : ∀ i, IsConnected (U i))
    (hdisj : Pairwise (fun i l ↦ Disjoint (U i) (U l)))
    (hpartner : ∀ x : G, f x = f (partner x))
    (hne : ∀ x : G, (x : E) ≠ partner x)
    (hunique : ∀ (x : G) (y : E), y ∈ S → f x = f y → (x : E) ≠ y →
      y = (partner x : E))
    (hmate : ∀ (i : I) (x : G), (x : E) ∈ U i → (partner x : E) ∈ U (mate i))
    (hKS : K ⊆ S) (hwhole : ∀ i, U i ⊆ K ∨ Disjoint (U i) K)
    (j : K → Y) (hj : Function.Injective j) (hc : Continuous j)
    (hnew : G' = j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y})
    (hmark : ∀ x : K, j x ∈ Q' ↔ (x : E) ∈ Q) :
    (ConnectedComponents.mk '' ((Subtype.val : G' → Y) ⁻¹' Q')).ncard =
      {i | U i ⊆ K ∧ U (mate i) ⊆ K ∧ (U i ∩ Q).Nonempty}.ncard ∧
    (ConnectedComponents.mk '' ((Subtype.val : G' → Y) ⁻¹' Q'))ᶜ.ncard =
      {i | U i ⊆ K ∧ U (mate i) ⊆ K ∧ Disjoint (U i) Q}.ncard := by
  let P (i : I) : Prop := U i ⊆ K ∧ U (mate i) ⊆ K
  let V (i : {i // P i}) : Set Y := j '' ((Subtype.val : K → E) ⁻¹' U i.val)
  have hnew' : ⋃ i, V i = G' := by
    rw [hnew, retained_double_locus_eq_paired_components U mate partner hG hcover
      hpartner hne hunique hmate hKS hwhole]
    simp only [preimage_iUnion, image_iUnion, V, P]
  obtain ⟨hv, hvdisj, hvmeet, hvavoid⟩ := retained_component_image_properties
    U P j hj hc hcompact hconn hdisj (fun _ h ↦ h.1) hmark
  have hcounts := connected_components_mark_counts_of_ambient_partition V
    (fun i ↦ (hv i).1.isClosed) hvdisj hnew' (fun i ↦ (hv i).2) Q'
  have hcount (p : I → Prop) :
      {i : {i // P i} | p i.val}.ncard = {i : I | P i ∧ p i}.ncard := by
    rw [← Set.ncard_image_of_injective _ (@Subtype.val_injective I P)]
    congr 1
    ext i
    simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right]
    constructor
    · rintro ⟨l, ⟨hl, hp⟩, rfl⟩
      exact ⟨hl, hp⟩
    · rintro ⟨hi, hp⟩
      exact ⟨i, ⟨hi, hp⟩, rfl⟩
  constructor
  · rw [hcounts.1]
    simp only [V, hvmeet]
    simpa only [P, and_assoc] using hcount (fun i ↦ (U i ∩ Q).Nonempty)
  · rw [hcounts.2]
    simp only [V, hvavoid]
    simpa only [P, and_assoc] using hcount (fun i ↦ Disjoint (U i) Q)



theorem retained_double_component_counts_decrease
    {E Y X I : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace Y] [T2Space Y] [Finite I]
    {S G K Q : Set E} {G' Q' : Set Y} {f : E → X}
    (U : I → Set E) (mate : I → I) (partner : G → G)
    (hG : G = {x | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y})
    (hcover : ⋃ i, U i = G)
    (hcompact : ∀ i, IsCompact (U i)) (hconn : ∀ i, IsConnected (U i))
    (hdisj : Pairwise (fun i l ↦ Disjoint (U i) (U l)))
    (hpartner : ∀ x : G, f x = f (partner x))
    (hne : ∀ x : G, (x : E) ≠ partner x)
    (hunique : ∀ (x : G) (y : E), y ∈ S → f x = f y → (x : E) ≠ y →
      y = (partner x : E))
    (hmate : ∀ (i : I) (x : G), (x : E) ∈ U i → (partner x : E) ∈ U (mate i))
    (hKS : K ⊆ S) (hwhole : ∀ i, U i ⊆ K ∨ Disjoint (U i) K)
    (j : K → Y) (hj : Function.Injective j) (hc : Continuous j)
    (hnew : G' = j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y})
    (hmark : ∀ x : K, j x ∈ Q' ↔ (x : E) ∈ Q)
    (i : I) (hiQ : (U i ∩ Q).Nonempty) (hiK : ¬ U i ⊆ K) :
    (ConnectedComponents.mk '' ((Subtype.val : G' → Y) ⁻¹' Q')).ncard <
      (ConnectedComponents.mk '' ((Subtype.val : G → E) ⁻¹' Q)).ncard ∧
    (ConnectedComponents.mk '' ((Subtype.val : G' → Y) ⁻¹' Q'))ᶜ.ncard ≤
      (ConnectedComponents.mk '' ((Subtype.val : G → E) ⁻¹' Q))ᶜ.ncard := by
  obtain ⟨hnewmark, hnewaway⟩ := retained_double_component_counts U mate partner
    hG hcover hcompact hconn hdisj hpartner hne hunique hmate hKS hwhole j hj hc hnew hmark
  obtain ⟨holdmark, holdaway⟩ := connected_components_mark_counts_of_ambient_partition
    U (fun i ↦ (hcompact i).isClosed) hdisj hcover hconn Q
  rw [hnewmark, hnewaway, holdmark, holdaway]
  constructor
  · apply Set.ncard_lt_ncard (ht := Set.toFinite _)
    refine ⟨fun _ h ↦ h.2.2, ?_⟩
    intro h
    exact hiK (h hiQ).1
  · exact Set.ncard_le_ncard (fun _ h ↦ h.2.2)




theorem retained_double_component_interior_counts_decrease
    {E Y X I : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace Y] [T2Space Y] [Finite I]
    {S G K Q : Set E} {G' Q' : Set Y} {f : E → X}
    (U : I → Set E) (mate : I → I) (partner : G → G)
    (hG : G = {x | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y})
    (hcover : ⋃ i, U i = G)
    (hcompact : ∀ i, IsCompact (U i)) (hconn : ∀ i, IsConnected (U i))
    (hdisj : Pairwise (fun i l ↦ Disjoint (U i) (U l)))
    (hpartner : ∀ x : G, f x = f (partner x))
    (hne : ∀ x : G, (x : E) ≠ partner x)
    (hunique : ∀ (x : G) (y : E), y ∈ S → f x = f y → (x : E) ≠ y →
      y = (partner x : E))
    (hmate : ∀ (i : I) (x : G), (x : E) ∈ U i → (partner x : E) ∈ U (mate i))
    (hKS : K ⊆ S) (hwhole : ∀ i, U i ⊆ K ∨ Disjoint (U i) K)
    (j : K → Y) (hj : Function.Injective j) (hc : Continuous j)
    (hnew : G' = j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y})
    (hmark : ∀ x : K, j x ∈ Q' ↔ (x : E) ∈ Q)
    (i : I) (hiQ : Disjoint (U i) Q) (hiK : ¬ U i ⊆ K) :
    (ConnectedComponents.mk '' ((Subtype.val : G' → Y) ⁻¹' Q')).ncard ≤
      (ConnectedComponents.mk '' ((Subtype.val : G → E) ⁻¹' Q)).ncard ∧
    (ConnectedComponents.mk '' ((Subtype.val : G' → Y) ⁻¹' Q'))ᶜ.ncard <
      (ConnectedComponents.mk '' ((Subtype.val : G → E) ⁻¹' Q))ᶜ.ncard := by
  obtain ⟨hnewmark, hnewaway⟩ := retained_double_component_counts U mate partner
    hG hcover hcompact hconn hdisj hpartner hne hunique hmate hKS hwhole j hj hc hnew hmark
  obtain ⟨holdmark, holdaway⟩ := connected_components_mark_counts_of_ambient_partition
    U (fun i ↦ (hcompact i).isClosed) hdisj hcover hconn Q
  rw [hnewmark, hnewaway, holdmark, holdaway]
  constructor
  · exact Set.ncard_le_ncard (fun _ h ↦ h.2.2)
  · apply Set.ncard_lt_ncard (ht := Set.toFinite _)
    refine ⟨fun _ h ↦ h.2.2, ?_⟩
    intro h
    exact hiK (h hiQ).1

end PoincareConjecture.M76.Dehn
