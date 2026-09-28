import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteMarkedFacePrefixes










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex



theorem exists_relative_face_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ (n : ℕ) (f : Fin n → Finset E),
      Function.Injective f ∧ range f = K.faces \ A.faces ∧
      ∀ i j, f j ⊂ f i → j < i := by
  classical
  let F := hK.toFinset.filter (fun s ↦ s ∉ A.faces)
  let rel : Finset E → Finset E → Prop := fun s t ↦ s.card ≤ t.card
  let : Std.Total rel := ⟨fun s t ↦ le_total s.card t.card⟩
  let : IsTrans (Finset E) rel := ⟨fun _ _ _ hst htu ↦ le_trans hst htu⟩
  let l := F.toList.mergeSort (rel · ·)
  have hperm : l.Perm F.toList := List.mergeSort_perm _ _
  have hnodup : l.Nodup := hperm.nodup_iff.mpr F.nodup_toList
  have hsorted : l.Pairwise rel := List.pairwise_mergeSort' rel _
  have hmem (s : Finset E) : s ∈ l ↔ s ∈ K.faces \ A.faces := by
    rw [hperm.mem_iff]
    simp only [Finset.mem_toList, F, Finset.mem_filter, hK.mem_toFinset, mem_sdiff]
  let f : Fin l.length → Finset E := l.get
  have hface (i : Fin l.length) : f i ∈ K.faces \ A.faces :=
    (hmem _).mp (List.mem_iff_get.mpr ⟨i, rfl⟩)
  have hmono : Monotone (fun i : Fin l.length ↦ (f i).card) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact hsorted.rel_get_of_lt hij
  refine ⟨l.length, f, hnodup.injective_get, ?_, ?_⟩
  · ext s
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ hface i,
      fun hs ↦ List.mem_iff_get.mp ((hmem s).mpr hs)⟩
  · intro i j hji
    by_contra hn
    exact (not_lt_of_ge (hmono (le_of_not_gt hn))) (Finset.card_lt_card hji)



theorem exists_relative_face_prefixes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    {n : ℕ} (f : Fin n → Finset E) (hfaces : range f = K.faces \ A.faces)
    (hbefore : ∀ i j, f j ⊂ f i → j < i) :
    ∃ P : ℕ → SimplicialComplex ℝ E,
      Monotone P ∧ (∀ k, (P k).faces.Finite ∧ P k ≤ K ∧ A ≤ P k) ∧
      P 0 = A ∧ P n = K ∧
      (∀ i : Fin n,
        (P (i.val + 1)).space = (P i.val).space ∪ convexHull ℝ (f i : Set E)) ∧
      ∀ i : Fin n, intrinsicFrontier ℝ (convexHull ℝ (f i : Set E)) ⊆ (P i.val).space := by
  classical
  have hface (i : Fin n) : f i ∈ K.faces := (hfaces.subset ⟨i, rfl⟩).1
  let P (k : ℕ) : SimplicialComplex ℝ E :=
    { faces := {σ | σ ∈ K.faces ∧
        (σ ∈ A.faces ∨ ∃ i : Fin n, i.val < k ∧ f i = σ)}
      indep := fun hσ ↦ K.indep hσ.1
      isRelLowerSet_faces := by
        intro σ hσ
        refine ⟨K.nonempty_of_mem_faces hσ.1, ?_⟩
        intro τ hτσ hτ
        have hτK := K.down_closed hσ.1 hτσ hτ
        refine ⟨hτK, ?_⟩
        by_cases hτA : τ ∈ A.faces
        · exact Or.inl hτA
        · right
          rcases hσ.2 with hσA | ⟨i, hi, rfl⟩
          · exact False.elim (hτA (A.down_closed hσA hτσ hτ))
          · by_cases heq : τ = f i
            · exact ⟨i, hi, heq.symm⟩
            · obtain ⟨j, rfl⟩ := hfaces.symm.subset ⟨hτK, hτA⟩
              exact ⟨j, lt_trans (hbefore i j
                (Finset.ssubset_iff_subset_ne.mpr ⟨hτσ, heq⟩)) hi, rfl⟩
      inter_subset_convexHull := fun hσ hτ ↦ K.inter_subset_convexHull hσ.1 hτ.1 }
  have hPK (k : ℕ) : P k ≤ K := fun _ hσ ↦ hσ.1
  have hAP (k : ℕ) : A ≤ P k := fun _ hσ ↦ ⟨hAK hσ, Or.inl hσ⟩
  have hmon : Monotone P := by
    intro k l hkl σ hσ
    refine ⟨hσ.1, hσ.2.imp id ?_⟩
    rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi.trans_le hkl, rfl⟩
  refine ⟨P, hmon, fun k ↦ ⟨hK.subset (hPK k), hPK k, hAP k⟩, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm _ (hAP 0)
    intro σ hσ
    rcases hσ.2 with hσ | ⟨i, hi, _⟩
    · exact hσ
    · exact False.elim (Nat.not_lt_zero _ hi)
  · apply le_antisymm (hPK n)
    intro σ hσ
    refine ⟨hσ, ?_⟩
    by_cases hσA : σ ∈ A.faces
    · exact Or.inl hσA
    · obtain ⟨i, rfl⟩ := hfaces.symm.subset ⟨hσ, hσA⟩
      exact Or.inr ⟨i, i.isLt, rfl⟩
  · intro i
    ext x
    constructor
    · intro hx
      obtain ⟨σ, hσ, hxσ⟩ := mem_space_iff.mp hx
      rcases hσ.2 with hσA | ⟨j, hj, rfl⟩
      · exact Or.inl (space_subset_of_le (hAP _) (A.convexHull_subset_space hσA hxσ))
      · by_cases hji : j.val < i.val
        · exact Or.inl (mem_space_iff.mpr ⟨f j, ⟨hface j, Or.inr ⟨j, hji, rfl⟩⟩, hxσ⟩)
        · have heq : j = i := Fin.ext (by omega)
          exact Or.inr (heq ▸ hxσ)
    · rintro (hx | hx)
      · exact space_subset_of_le (hmon (Nat.le_succ _)) hx
      · exact mem_space_iff.mpr
          ⟨f i, ⟨hface i, Or.inr ⟨i, Nat.lt_succ_self _, rfl⟩⟩, hx⟩
  · intro i x hx
    obtain ⟨a, ha, hproper, hxa⟩ := K.exists_properFace_of_mem_intrinsicFrontier (hface i) hx
    by_cases haA : a ∈ A.faces
    · exact space_subset_of_le (hAP _) (A.convexHull_subset_space haA hxa)
    · obtain ⟨k, rfl⟩ := hfaces.symm.subset ⟨ha, haA⟩
      exact mem_space_iff.mpr
        ⟨f k, ⟨hface k, Or.inr ⟨k, hbefore i k hproper, rfl⟩⟩, hxa⟩

end Geometry.SimplicialComplex
