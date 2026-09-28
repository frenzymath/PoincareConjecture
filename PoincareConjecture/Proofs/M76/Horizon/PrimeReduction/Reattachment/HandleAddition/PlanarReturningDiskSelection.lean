import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OutermostProperArc









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)

theorem exists_outermost_planar_returning_disk
    {ι : Type*} [Finite ι] (W : ι → Set P2) (a b : ι → P2)
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {a i,b i})
    (hab : ∀ i, a i ≠ b i) (hdis : Pairwise fun i j => Disjoint (W i) (W j))
    {K B D E U : Set P2}
    (hWK : ∀ i, W i ⊆ K) (haB : ∀ i, a i ∈ B) (hbB : ∀ i, b i ∈ B)
    (hproper : ∀ i, W i \ {a i,b i} ⊆ K \ B)
    (i : ι) (hD : IsFinitePLBallPair P2 D (U ∪ W i))
    (hU : IsFinitePLBallPair ℝ U {a i,b i})
    (hDB : D ∩ B = U)
    (hE : IsClosed E) (hcover : K ⊆ D ∪ E) (hDE : D ∩ E = W i) :
    ∃ j, ∃ A V : Set P2,
      IsFinitePLBallPair P2 A (V ∪ W j) ∧
      IsFinitePLBallPair ℝ V {a j,b j} ∧
      A ⊆ D ∧ A ∩ B = V ∧ V ∩ W j = {a j,b j} ∧
      A ∩ (⋃ k,W k) = W j ∧ ∀ k, k ≠ j → Disjoint A (W k) := by
  classical
  let := Fintype.ofFinite ι
  let I := Finset.univ.filter (fun j => j ≠ i ∧ W j ⊆ D)
  have hside (j : ι) (hji : j ≠ i) : W j ⊆ D ∨ W j ⊆ E :=
    Dehn.isPreconnected_subset_one_cut_piece (hW j).isConnected.isPreconnected
      hD.isCompact.isClosed hE ((hWK j).trans hcover) hDE (hdis hji)
  have hout (j : ι) (hji : j ≠ i) (hj : j ∉ I) : Disjoint D (W j) := by
    have hnD : ¬ W j ⊆ D := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hji,h⟩)
    have hjE := (hside j hji).resolve_left hnD
    exact disjoint_left.mpr fun x hxD hxW =>
      disjoint_left.mp (hdis hji) hxW (hDE.subset ⟨hxD,hjE hxW⟩)
  have hpiece : ∀ j ∈ I, W j ⊆ D := fun _ hj => (Finset.mem_filter.mp hj).2.2
  have hne : ∀ j ∈ I, j ≠ i := fun _ hj => (Finset.mem_filter.mp hj).2.1
  have hends : ∀ j ∈ I, {a j,b j} ⊆ U := by
    intro j hj x hx
    refine hDB.subset ⟨hpiece j hj ((hW j).1 hx),?_⟩
    rcases hx with rfl | rfl
    · exact haB j
    · exact hbB j
  have hproperD : ∀ j ∈ I, W j \ {a j,b j} ⊆ D \ (U ∪ W i) := by
    intro j hj x hx
    refine ⟨hpiece j hj hx.1,?_⟩
    rintro (hxU | hxWi)
    · exact (hproper j hx).2 (hDB.symm.subset hxU).2
    · exact disjoint_left.mp (hdis (hne j hj)) hx.1 hxWi
  have htotal {j : ι} {A : Set P2} (hjA : W j ⊆ A)
      (havoid : ∀ k, k ≠ j → Disjoint A (W k)) : A ∩ (⋃ k,W k) = W j := by
    apply Subset.antisymm
    · rintro x ⟨hxA,hx⟩
      obtain ⟨k,hxk⟩ := mem_iUnion.mp hx
      by_cases hkj : k = j
      · exact hkj ▸ hxk
      · exact (disjoint_left.mp (havoid k hkj) hxA hxk).elim
    · exact fun x hx => ⟨hjA hx,mem_iUnion.mpr ⟨j,hx⟩⟩
  by_cases hIn : I.Nonempty
  · obtain ⟨j,hj,A,V,hA,hV,hAD,hAV,hAWi,havoid⟩ :=
      exists_outermost_proper_arc_disk I W a b (fun j _ => hW j)
        (fun j _ => hab j) (fun _ _ _ _ hij => hdis hij) hD
        (fun j hj => Or.inl (hends j hj (Or.inl rfl)))
        (fun j hj => Or.inl (hends j hj (Or.inr rfl))) hproperD
        (hW i).isConnected.isPreconnected (fun _ hx => hD.1 (Or.inr hx))
        (fun j hj => hdis (hne j hj).symm) hIn
    have hAB : A ∩ B = V := by
      apply Subset.antisymm
      · intro x hx
        exact hAV.subset ⟨hx.1,Or.inl (hDB.subset ⟨hAD hx.1,hx.2⟩)⟩
      · intro x hx
        have hh := hAV.symm.subset hx
        refine ⟨hh.1,?_⟩
        rcases hh.2 with hxU | hxW
        · exact (hDB.symm.subset hxU).2
        · exact (disjoint_left.mp hAWi hh.1 hxW).elim
    have hall : ∀ k, k ≠ j → Disjoint A (W k) := by
      intro k hkj
      by_cases hki : k = i
      · exact hki ▸ hAWi
      by_cases hkI : k ∈ I
      · exact havoid k hkI hkj
      · exact (hout k hki hkI).mono_left hAD
    refine ⟨j,A,V,hA,hV,hAD,hAB,?_,htotal (fun _ hx => hA.1 (Or.inr hx)) hall,hall⟩
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproper j ⟨hx.2,hn⟩).2 (hAB.symm.subset hx.1).2
    · exact fun x hx => ⟨hV.1 hx,(hW j).1 hx⟩
  · have hall : ∀ k, k ≠ i → Disjoint D (W k) :=
      fun k hki => hout k hki (fun hk => hIn ⟨k,hk⟩)
    refine ⟨i,D,U,hD,hU,Subset.rfl,hDB,?_,
      htotal (fun _ hx => hD.1 (Or.inr hx)) hall,hall⟩
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproper i ⟨hx.2,hn⟩).2 (hDB.symm.subset hx.1).2
    · exact fun x hx => ⟨hU.1 hx,(hW i).1 hx⟩

end PoincareConjecture.M76
