import Mathlib.Topology.Constructions










set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X]



theorem isOpen_preimage_val_of_open_neighborhood {s d u a : Set X}
    (hu : IsOpen ((Subtype.val : s → X) ⁻¹' u)) (hau : a ⊆ u) (hud : u ⊆ d)
    (ha : IsOpen ((Subtype.val : d → X) ⁻¹' a)) :
    IsOpen ((Subtype.val : s → X) ⁻¹' a) := by
  obtain ⟨v, hv, he⟩ := isOpen_induced_iff.mp ha
  have hmem (x : d) : (x : X) ∈ v ↔ (x : X) ∈ a := by
    exact Set.ext_iff.mp he x
  have heq : (Subtype.val : s → X) ⁻¹' a =
      ((Subtype.val : s → X) ⁻¹' u) ∩ ((Subtype.val : s → X) ⁻¹' v) := by
    ext x
    constructor
    · intro hx
      exact ⟨hau hx, (hmem ⟨x, hud (hau hx)⟩).mpr hx⟩
    · intro hx
      exact (hmem ⟨x, hud hx.1⟩).mp hx.2
  rw [heq]
  exact hu.inter (hv.preimage continuous_subtype_val)




theorem interior_preimage_val_of_subset_interior {d a : Set X}
    (ha : a ⊆ interior d) :
    interior ((Subtype.val : d → X) ⁻¹' a) = (Subtype.val : d → X) ⁻¹' interior a := by
  apply Subset.antisymm
  · intro x hx
    have hxa : (x : X) ∈ a := (interior_subset hx : x ∈ (Subtype.val : d → X) ⁻¹' a)
    obtain ⟨v, hv, he⟩ := isOpen_induced_iff.mp
      (isOpen_interior : IsOpen (interior ((Subtype.val : d → X) ⁻¹' a)))
    have hmem (y : d) : (y : X) ∈ v ↔ y ∈ interior ((Subtype.val : d → X) ⁻¹' a) :=
      Set.ext_iff.mp he y
    apply mem_interior.mpr
    refine ⟨v ∩ interior d, ?_, hv.inter isOpen_interior,
      ⟨(hmem x).mpr hx, ha hxa⟩⟩
    intro y hy
    have hyi := (hmem ⟨y, interior_subset hy.2⟩).mp hy.1
    exact (interior_subset hyi : (⟨y, interior_subset hy.2⟩ : d) ∈
      (Subtype.val : d → X) ⁻¹' a)
  · exact preimage_interior_subset_interior_preimage continuous_subtype_val




theorem interior_preimage_val_of_open_neighborhood {s d u a b : Set X}
    (hds : d ⊆ s) (had : a ⊆ d) (hba : b ⊆ a)
    (hu : IsOpen ((Subtype.val : s → X) ⁻¹' u)) (hbu : b ⊆ u) (hud : u ⊆ d)
    (hint : interior ((Subtype.val : d → X) ⁻¹' a) =
      (Subtype.val : d → X) ⁻¹' b) :
    interior ((Subtype.val : s → X) ⁻¹' a) = (Subtype.val : s → X) ⁻¹' b := by
  have hb : IsOpen ((Subtype.val : d → X) ⁻¹' b) := hint ▸ isOpen_interior
  have hbs := isOpen_preimage_val_of_open_neighborhood hu hbu hud hb
  apply Subset.antisymm
  · intro x hx
    have hxa : (x : X) ∈ a := (interior_subset hx : x ∈ (Subtype.val : s → X) ⁻¹' a)
    let y : d := ⟨x, had hxa⟩
    have hc : Continuous (Set.inclusion hds) := continuous_subtype_val.subtype_mk _
    have hy : y ∈ interior ((Subtype.val : d → X) ⁻¹' a) :=
      preimage_interior_subset_interior_preimage hc
        (t := (Subtype.val : s → X) ⁻¹' a) (a := y) hx
    rwa [hint] at hy
  · exact interior_maximal (preimage_mono hba) hbs




theorem interior_preimage_val_inclusion_of_open_neighborhood {s d u a : Set X}
    (hds : d ⊆ s) (hu : IsOpen ((Subtype.val : s → X) ⁻¹' u))
    (hau : a ⊆ u) (hud : u ⊆ d) :
    interior ((Subtype.val : d → X) ⁻¹' a) =
      Set.inclusion hds ⁻¹' interior ((Subtype.val : s → X) ⁻¹' a) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨v, hv, he⟩ := isOpen_induced_iff.mp
      (isOpen_interior : IsOpen (interior ((Subtype.val : d → X) ⁻¹' a)))
    have hmem (y : d) : (y : X) ∈ v ↔ y ∈ interior ((Subtype.val : d → X) ⁻¹' a) :=
      Set.ext_iff.mp he y
    have hxa : (x : X) ∈ a := (interior_subset hx : x ∈ (Subtype.val : d → X) ⁻¹' a)
    apply mem_interior.mpr
    refine ⟨((Subtype.val : s → X) ⁻¹' u) ∩ ((Subtype.val : s → X) ⁻¹' v), ?_,
      hu.inter (hv.preimage continuous_subtype_val), ⟨hau hxa, (hmem x).mpr hx⟩⟩
    intro y hy
    have hyi := (hmem ⟨y, hud hy.1⟩).mp hy.2
    exact (interior_subset hyi : (⟨y, hud hy.1⟩ : d) ∈ (Subtype.val : d → X) ⁻¹' a)
  · have hc : Continuous (Set.inclusion hds) := continuous_subtype_val.subtype_mk _
    exact preimage_interior_subset_interior_preimage hc

end Set




theorem IsClosed.closure_eq_of_preimage_val {X : Type*} [TopologicalSpace X]
    {s a b : Set X} (hs : IsClosed s) (ha : a ⊆ s) (hb : b ⊆ s)
    (hcl : closure ((Subtype.val : s → X) ⁻¹' a) = (Subtype.val : s → X) ⁻¹' b) :
    closure a = b := by
  have hca : closure a ⊆ s := closure_minimal ha hs
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    image_preimage_eq_of_subset (by simpa using ha)] at hcl
  apply Subset.antisymm
  · intro x hx
    exact Set.ext_iff.mp hcl ⟨x, hca hx⟩ |>.mp hx
  · intro x hx
    exact Set.ext_iff.mp hcl ⟨x, hb hx⟩ |>.mpr hx
