import PoincareConjecture.Proofs.M76.Triangulation.HamiltonSimplexOrder
import Mathlib.Data.Finset.Lattice.Fold










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex





theorem exists_marked_face_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K) :
    ∃ (n : ℕ) (f : Fin n → Finset E),
      Function.Injective f ∧ range f = K.faces ∧
      (∀ i j, f j ⊂ f i → j < i) ∧
      (∀ i j, j < i → f i ∈ A.faces → f j ∈ A.faces) ∧
      (⋃ i, convexHull ℝ (f i : Set E)) = K.space ∧
      ∀ i : Fin n,
        IsCompact (⋃ j ∈ Iio i, convexHull ℝ (f j : Set E)) ∧
        intrinsicFrontier ℝ (convexHull ℝ (f i : Set E)) ⊆
          ⋃ j ∈ Iio i, convexHull ℝ (f j : Set E) ∧
        Disjoint (⋃ j ∈ Iio i, convexHull ℝ (f j : Set E))
          (intrinsicInterior ℝ (convexHull ℝ (f i : Set E))) := by
  classical
  let N : ℕ := hK.toFinset.sup Finset.card
  have hbound {s : Finset E} (hs : s ∈ K.faces) : s.card ≤ N :=
    Finset.le_sup (hK.mem_toFinset.mpr hs)
  let w (s : Finset E) : ℕ := if s ∈ A.faces then s.card else N + 1 + s.card
  have hproper {s t : Finset E} (hs : s ∈ K.faces)
      (hst : s ⊂ t) : w s < w t := by
    have hcard := Finset.card_lt_card hst
    by_cases htA : t ∈ A.faces
    · have hsA : s ∈ A.faces := A.down_closed htA hst.le (K.nonempty_of_mem_faces hs)
      simpa only [w, if_pos hsA, if_pos htA] using hcard
    · by_cases hsA : s ∈ A.faces
      · have hsbound := hbound hs
        simp only [w, if_pos hsA, if_neg htA]
        omega
      · simpa only [w, if_neg hsA, if_neg htA] using Nat.add_lt_add_left hcard (N + 1)
  let rel : Finset E → Finset E → Prop := fun s t => w s ≤ w t
  let : Std.Total rel := ⟨fun s t => le_total (w s) (w t)⟩
  let : IsTrans (Finset E) rel := ⟨fun _ _ _ hst htu => le_trans hst htu⟩
  let l : List (Finset E) := hK.toFinset.toList.mergeSort (rel · ·)
  have hperm : l.Perm hK.toFinset.toList := List.mergeSort_perm _ _
  have hnodup : l.Nodup := hperm.nodup_iff.mpr hK.toFinset.nodup_toList
  have hsorted : l.Pairwise rel := List.pairwise_mergeSort' rel _
  have hmem (s : Finset E) : s ∈ l ↔ s ∈ K.faces := by
    rw [hperm.mem_iff]
    simp only [Finset.mem_toList, hK.mem_toFinset]
  let f : Fin l.length → Finset E := l.get
  have hinj : Function.Injective f := hnodup.injective_get
  have hface (i : Fin l.length) : f i ∈ K.faces :=
    (hmem _).mp (List.mem_iff_get.mpr ⟨i, rfl⟩)
  have hsurj (s : Finset E) (hs : s ∈ K.faces) : ∃ i, f i = s :=
    List.mem_iff_get.mp ((hmem s).mpr hs)
  have hmono : Monotone (fun i : Fin l.length => w (f i)) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact hsorted.rel_get_of_lt hij
  have hbefore (i j : Fin l.length) (hji : f j ⊂ f i) : j < i := by
    by_contra hn
    exact (not_lt_of_ge (hmono (le_of_not_gt hn)))
      (hproper (hface j) hji)
  refine ⟨l.length, f, hinj, ?_, hbefore, ?_, ?_, ?_⟩
  · ext s
    exact ⟨fun ⟨i, hi⟩ => hi ▸ hface i, hsurj s⟩
  · intro i j hji hiA
    by_contra hjA
    have hle := hmono hji.le
    have hibound := hbound (hAK hiA)
    simp only [w, if_pos hiA, if_neg hjA] at hle
    omega
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
      obtain ⟨s, hs, hsproper, hxs⟩ :=
        K.exists_properFace_of_mem_intrinsicFrontier (hface i) hx
      obtain ⟨j, rfl⟩ := hsurj s hs
      exact mem_iUnion₂.mpr ⟨j, hbefore i j hsproper, hxs⟩
    · apply disjoint_left.mpr
      intro x hx hxint
      obtain ⟨j, hji, hxj⟩ := mem_iUnion₂.mp hx
      have hne : f i ≠ f j := fun heq => (ne_of_gt hji) (hinj heq)
      have hnsub : ¬f i ⊆ f j := by
        intro hsub
        exact (not_lt_of_ge hji.le) (hbefore j i
          (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩))
      have hproper' : f j ∩ f i ⊂ f i :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,
          fun heq => hnsub (heq ▸ Finset.inter_subset_left)⟩
      have hxinter : x ∈ convexHull ℝ ((f j ∩ f i : Finset E) : Set E) := by
        simpa only [Finset.coe_inter] using
          (K.inter_subset_convexHull (hface j) (hface i)
            ⟨hxj, intrinsicInterior_subset hxint⟩)
      have hxfront := (K.indep (hface i)).convexHull_subset_intrinsicFrontier
        hproper' hxinter
      rw [← intrinsicClosure_sdiff_intrinsicInterior] at hxfront
      exact hxfront.2 hxint

end Geometry.SimplicialComplex
