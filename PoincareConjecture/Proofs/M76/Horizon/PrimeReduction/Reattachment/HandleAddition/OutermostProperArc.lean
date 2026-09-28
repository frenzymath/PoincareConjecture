import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

private theorem exists_proper_arc_cut_away
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C q W K : Set E} {a b : E}
    (hC : IsFinitePLBallPair (ℝ × ℝ) C q)
    (hW : IsFinitePLBallPair ℝ W {a,b}) (ha : a ∈ q) (hb : b ∈ q) (hab : a ≠ b)
    (hproper : W \ {a,b} ⊆ C \ q) (hK : IsPreconnected K)
    (hKC : K ⊆ C) (hKW : Disjoint K W) :
    ∃ A B U V : Set E,
      IsFinitePLBallPair (ℝ × ℝ) A (U ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) B (V ∪ W) ∧
      IsFinitePLBallPair ℝ U {a,b} ∧ IsFinitePLBallPair ℝ V {a,b} ∧
      A ∪ B = C ∧ A ∩ B = W ∧ A ∩ q = U ∧ B ∩ q = V ∧ Disjoint A K := by
  obtain ⟨U,V,hU,hV,hUq,hUV⟩ := hC.exists_boundary_arcs ha hb hab
  obtain ⟨A,B,hA,hB,hAB,hABi,hAq,hBq⟩ :=
    hC.exists_proper_arc_cut hU hV hW hab hUV.subset hUq hproper
  have hB' : IsFinitePLBallPair (ℝ × ℝ) B (V ∪ W) := by simpa only [union_comm] using hB
  rcases Dehn.isPreconnected_subset_one_cut_piece hK hA.isCompact.isClosed
      hB.isCompact.isClosed (hKC.trans hAB.symm.subset) hABi hKW with hKA | hKB
  · refine ⟨B,A,V,U,hB',hA,hV,hU,(union_comm _ _).trans hAB,
      (inter_comm _ _).trans hABi,hBq,hAq,?_⟩
    exact disjoint_left.mpr (fun x hxB hxK => disjoint_left.mp hKW hxK
      (hABi.subset ⟨hKA hxK,hxB⟩))
  · refine ⟨A,B,U,V,hA,hB',hU,hV,hAB,hABi,hAq,hBq,?_⟩
    exact disjoint_left.mpr (fun x hxA hxK => disjoint_left.mp hKW hxK
      (hABi.subset ⟨hxA,hKB hxK⟩))



theorem exists_outermost_proper_arc_disk
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (I : Finset ι) (W : ι → Set E) (a b : ι → E)
    (hW : ∀ i ∈ I, IsFinitePLBallPair ℝ (W i) {a i,b i})
    (hab : ∀ i ∈ I, a i ≠ b i)
    (hdis : (I : Set ι).Pairwise fun i j => Disjoint (W i) (W j))
    {C q K : Set E} (hC : IsFinitePLBallPair (ℝ × ℝ) C q)
    (ha : ∀ i ∈ I, a i ∈ q) (hb : ∀ i ∈ I, b i ∈ q)
    (hproper : ∀ i ∈ I, W i \ {a i,b i} ⊆ C \ q)
    (hK : IsPreconnected K) (hKC : K ⊆ C)
    (hKW : ∀ i ∈ I, Disjoint K (W i)) (hne : I.Nonempty) :
    ∃ i ∈ I, ∃ A U : Set E,
      IsFinitePLBallPair (ℝ × ℝ) A (U ∪ W i) ∧
      IsFinitePLBallPair ℝ U {a i,b i} ∧
      A ⊆ C ∧ A ∩ q = U ∧ Disjoint A K ∧
      ∀ j ∈ I, j ≠ i → Disjoint A (W j) := by
  classical
  induction I using Finset.strongInductionOn generalizing C q K with
  | _ I ih =>
    obtain ⟨i,hi⟩ := hne
    obtain ⟨A,B,U,V,hA,hB,hU,hV,hAB,hABi,hAq,hBq,hAK⟩ :=
      exists_proper_arc_cut_away hC (hW i hi) (ha i hi) (hb i hi) (hab i hi)
        (hproper i hi) hK hKC (hKW i hi)
    have hAC : A ⊆ C := subset_union_left.trans hAB.subset
    have hBC : B ⊆ C := subset_union_right.trans hAB.subset
    have hWC (j : ι) (hj : j ∈ I) : W j ⊆ C := by
      intro x hx
      by_cases hm : x ∈ ({a j,b j} : Set E)
      · exact hC.1 (by rcases hm with rfl | rfl; exact ha j hj; exact hb j hj)
      · exact (hproper j hj ⟨hx,hm⟩).1
    have hside (j : ι) (hj : j ∈ I) (hji : j ≠ i) : W j ⊆ A ∨ W j ⊆ B :=
      Dehn.isPreconnected_subset_one_cut_piece (hW j hj).isConnected.isPreconnected
        hA.isCompact.isClosed hB.isCompact.isClosed ((hWC j hj).trans hAB.symm.subset)
        hABi (hdis hj hi hji)
    let J := I.filter (fun j => j ≠ i ∧ W j ⊆ A)
    have hJI : J ⊆ I := Finset.filter_subset _ _
    have hnoti : i ∉ J := by simp [J]
    have hJlt : J ⊂ I := Finset.ssubset_iff_subset_ne.mpr
      ⟨hJI,fun h => hnoti (h.symm ▸ hi)⟩
    have hout (j : ι) (hj : j ∈ I) (hji : j ≠ i) (hjJ : j ∉ J) : Disjoint A (W j) := by
      have hnA : ¬ W j ⊆ A := fun h => hjJ (Finset.mem_filter.mpr ⟨hj,hji,h⟩)
      have hjB : W j ⊆ B := (hside j hj hji).resolve_left hnA
      exact disjoint_left.mpr (fun x hxA hxW => disjoint_left.mp (hdis hi hj hji.symm)
        (hABi.subset ⟨hxA,hjB hxW⟩) hxW)
    by_cases hJe : J.Nonempty
    · have hJA (j : ι) (hj : j ∈ J) : W j ⊆ A := (Finset.mem_filter.mp hj).2.2
      have hJne (j : ι) (hj : j ∈ J) : j ≠ i := (Finset.mem_filter.mp hj).2.1
      have hJU (j : ι) (hj : j ∈ J) : {a j,b j} ⊆ U := by
        intro x hx
        apply hAq.subset
        refine ⟨hJA j hj ((hW j (hJI hj)).1 hx),?_⟩
        rcases hx with rfl | rfl
        · exact ha j (hJI hj)
        · exact hb j (hJI hj)
      have hJproper (j : ι) (hj : j ∈ J) : W j \ {a j,b j} ⊆ A \ (U ∪ W i) := by
        intro x hx
        refine ⟨hJA j hj hx.1,?_⟩
        rintro (hxU | hxWi)
        · exact (hproper j (hJI hj) hx).2 (hAq.symm.subset hxU).2
        · exact disjoint_left.mp (hdis (hJI hj) hi (hJne j hj)) hx.1 hxWi
      obtain ⟨k,hk,Q,T,hQ,hT,hQA,hQT,hQW,havoid⟩ := ih J hJlt
        (fun j hj => hW j (hJI hj)) (fun j hj => hab j (hJI hj))
        (hdis.mono hJI) hA
        (fun j hj => Or.inl (hJU j hj (by simp)))
        (fun j hj => Or.inl (hJU j hj (by simp))) hJproper
        (hW i hi).isConnected.isPreconnected (fun _ hx => hA.1 (Or.inr hx))
        (fun j hj => hdis hi (hJI hj) (hJne j hj).symm) hJe
      have hTq : Q ∩ q = T := by
        rw [←hQT]
        ext x
        constructor
        · exact fun hx => ⟨hx.1,Or.inl (hAq.subset ⟨hQA hx.1,hx.2⟩)⟩
        · rintro ⟨hxQ,hxU | hxW⟩
          · exact ⟨hxQ,(hAq.symm.subset hxU).2⟩
          · exact (disjoint_left.mp hQW hxQ hxW).elim
      refine ⟨k,hJI hk,Q,T,hQ,hT,hQA.trans hAC,hTq,hAK.mono_left hQA,?_⟩
      intro j hj hjk
      by_cases hji : j = i
      · subst j
        exact hQW
      by_cases hjJ : j ∈ J
      · exact havoid j hjJ hjk
      · exact (hout j hj hji hjJ).mono_left hQA
    · refine ⟨i,hi,A,U,hA,hU,hAC,hAq,hAK,?_⟩
      intro j hj hji
      exact hout j hj hji (fun hjJ => hJe ⟨j,hjJ⟩)




theorem exists_outermost_proper_arc_disk_with_contact
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (I : Finset ι) (W : ι → Set E) (a b : ι → E)
    (hW : ∀ i ∈ I, IsFinitePLBallPair ℝ (W i) {a i,b i})
    (hab : ∀ i ∈ I, a i ≠ b i)
    (hdis : (I : Set ι).Pairwise fun i j => Disjoint (W i) (W j))
    {C q : Set E} (hC : IsFinitePLBallPair (ℝ × ℝ) C q)
    (ha : ∀ i ∈ I, a i ∈ q) (hb : ∀ i ∈ I, b i ∈ q)
    (hproper : ∀ i ∈ I, W i \ {a i,b i} ⊆ C \ q) (hne : I.Nonempty) :
    ∃ i ∈ I, ∃ A U : Set E,
      IsFinitePLBallPair (ℝ × ℝ) A (U ∪ W i) ∧
      IsFinitePLBallPair ℝ U {a i,b i} ∧ A ⊆ C ∧ A ∩ q = U ∧
      U ∩ W i = {a i,b i} ∧ A ∩ (⋃ j ∈ I, W j) = W i ∧
      Disjoint (A \ (U ∪ W i)) (⋃ j ∈ I, W j) := by
  obtain ⟨i,hi,A,U,hA,hU,hAC,hAq,_,havoid⟩ :=
    exists_outermost_proper_arc_disk I W a b hW hab hdis hC ha hb hproper
      isPreconnected_empty (empty_subset C) (fun _ _ => empty_disjoint _) hne
  have hUW : U ∩ W i = {a i,b i} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproper i hi ⟨hx.2,hn⟩).2 (hAq.symm.subset hx.1).2
    · exact fun x hx => ⟨hU.1 hx,(hW i hi).1 hx⟩
  have hcontact : A ∩ (⋃ j ∈ I, W j) = W i := by
    apply Subset.antisymm
    · rintro x ⟨hxA,hx⟩
      obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
      by_cases hji : j = i
      · simpa only [hji] using hxj
      · exact (disjoint_left.mp (havoid j hj hji) hxA hxj).elim
    · exact fun x hx => ⟨hA.1 (Or.inr hx),mem_iUnion₂.mpr ⟨i,hi,hx⟩⟩
  refine ⟨i,hi,A,U,hA,hU,hAC,hAq,hUW,hcontact,?_⟩
  exact disjoint_left.mpr (fun x hx hy => hx.2 (Or.inr (hcontact.subset ⟨hx.1,hy⟩)))

end PoincareConjecture.M76

