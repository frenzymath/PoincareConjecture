import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFrontierAttachment
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_hamilton_face_order (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) :
    ∃ (n : ℕ) (f : Fin n → Finset E),
      Function.Injective f ∧ range f = K.faces ∧
      Monotone (fun i => (f i).card) ∧
      (⋃ i, convexHull ℝ (f i : Set E)) = K.space ∧
      ∀ i : Fin n,
        IsCompact (⋃ j ∈ Iio i, convexHull ℝ (f j : Set E)) ∧
        intrinsicFrontier ℝ (convexHull ℝ (f i : Set E)) ⊆
          ⋃ j ∈ Iio i, convexHull ℝ (f j : Set E) ∧
        Disjoint (⋃ j ∈ Iio i, convexHull ℝ (f j : Set E))
          (intrinsicInterior ℝ (convexHull ℝ (f i : Set E))) := by
  classical
  let r : Finset E → Finset E → Prop := fun s t => s.card ≤ t.card
  let : Std.Total r := ⟨fun s t => le_total s.card t.card⟩
  let : IsTrans (Finset E) r := ⟨fun _ _ _ hst htu => le_trans hst htu⟩
  let l : List (Finset E) := hK.toFinset.toList.mergeSort (r · ·)
  have hlperm : l.Perm hK.toFinset.toList := List.mergeSort_perm _ _
  have hlnodup : l.Nodup := hlperm.nodup_iff.mpr hK.toFinset.nodup_toList
  have hlsorted : l.Pairwise r := List.pairwise_mergeSort' r _
  have hlmem (s : Finset E) : s ∈ l ↔ s ∈ K.faces := by
    rw [hlperm.mem_iff]
    simp only [Finset.mem_toList, hK.mem_toFinset]
  let f : Fin l.length → Finset E := l.get
  have hinj : Function.Injective f := hlnodup.injective_get
  have hface (i : Fin l.length) : f i ∈ K.faces :=
    (hlmem _).mp (List.mem_iff_get.mpr ⟨i, rfl⟩)
  have hsurj (s : Finset E) (hs : s ∈ K.faces) : ∃ i, f i = s :=
    List.mem_iff_get.mp ((hlmem s).mpr hs)
  have hmono : Monotone (fun i : Fin l.length => (f i).card) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact hlsorted.rel_get_of_lt hij
  refine ⟨l.length, f, hinj, ?_, hmono, ?_, ?_⟩
  · ext s
    exact ⟨fun ⟨i, hi⟩ => hi ▸ hface i, hsurj s⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact K.convexHull_subset_space (hface i) hi
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      obtain ⟨i, rfl⟩ := hsurj s hs
      exact mem_iUnion.mpr ⟨i, hxs⟩
  · intro i
    refine ⟨(Set.finite_univ.subset (subset_univ (Iio i))).isCompact_biUnion
      (fun j _ => (f j).finite_toSet.isCompact_convexHull ℝ), ?_, ?_⟩
    · intro x hx
      obtain ⟨s, hs, hproper, hxs⟩ :=
        K.exists_properFace_of_mem_intrinsicFrontier (hface i) hx
      obtain ⟨j, rfl⟩ := hsurj s hs
      have hji : j < i := by
        by_contra hji
        have hle := hmono (le_of_not_gt hji)
        exact (not_lt_of_ge hle) (Finset.card_lt_card hproper)
      exact mem_iUnion₂.mpr ⟨j, hji, hxs⟩
    · apply disjoint_left.mpr
      intro x hx hxint
      obtain ⟨j, hji, hxj⟩ := mem_iUnion₂.mp hx
      have hne : f j ≠ f i := fun heq => (ne_of_lt hji) (hinj heq)
      have hxfront := K.inter_subset_intrinsicFrontier_of_card_le
        (hface i) (hface j) hne (hmono hji.le)
          ⟨hxj, intrinsicInterior_subset hxint⟩
      rw [← intrinsicClosure_sdiff_intrinsicInterior] at hxfront
      exact hxfront.2 hxint

end Geometry.SimplicialComplex
