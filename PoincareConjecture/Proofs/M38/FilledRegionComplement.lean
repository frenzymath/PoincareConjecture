import PoincareConjecture.Proofs.M38.FiniteBallComplement
import PoincareConjecture.Proofs.M38.ClosedSetNesting











set_option autoImplicit false

open Set Topology

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} {ι : Type*} [Finite ι]
  {U : Set A.carrier}



theorem region_eq_complement_of_avoiding_fillings
    (hA : IsPreconnected (univ : Set A.carrier))
    (hU : IsOpen U) (hconnected : IsConnected U)
    (B : ι → SurgeryBallEmbedding A)
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (frontier (B i).closedBall) (frontier (B j).closedBall))
    (hfrontier : frontier U = ⋃ i, frontier (B i).closedBall)
    (p : A.carrier) (hp : p ∈ U) (hpB : ∀ i, p ∉ (B i).closedBall) :
    (∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall) ∧
      U = (⋃ i, (B i).closedBall)ᶜ := by
  classical
  have hclosed (i) : IsClosed (B i).closedBall :=
    (surgeryBall_closedImage_compact (B i) 1 (by norm_num)).isClosed
  have hUfront (i) : Disjoint U (frontier (B i).closedBall) := by
    apply disjoint_left.mpr
    intro y hy hyf
    have hyfront : y ∈ frontier U := hfrontier.symm ▸ mem_iUnion.mpr ⟨i, hyf⟩
    exact hyfront.2 (hU.interior_eq.symm ▸ hy)
  have hUB (i) : U ⊆ (B i).closedBallᶜ := by
    rcases preconnected_subset_interior_or_compl (hclosed i) hconnected.isPreconnected
        (hUfront i) with hin | hout
    · exact (hpB i (interior_subset (hin hp))).elim
    · exact hout
  have hfrontclosure (i) : frontier (B i).closedBall ⊆ closure U := by
    intro y hy
    exact frontier_subset_closure (hfrontier.symm ▸ mem_iUnion.mpr ⟨i, hy⟩)
  have hcloutside (i) : closure U ⊆ (interior (B i).closedBall)ᶜ :=
    closure_minimal (fun y hy h => hUB i hy (interior_subset h)) isOpen_interior.isClosed_compl
  have hBout (i) : IsPreconnected (B i).closedBallᶜ := by
    simpa only [iUnion_const] using (surgeryBall_iUnion_complement_connected hA
      (fun _ : Fin 1 => B i) (fun j k hjk => (hjk (Subsingleton.elim j k)).elim)
      p (fun _ => hpB i)).isPreconnected
  have hsep (i j : ι) (hij : i ≠ j) : Disjoint (B i).closedBall (B j).closedBall := by
    have hnested (k l : ι)
        (hkl : Disjoint (frontier (B k).closedBall) (frontier (B l).closedBall))
        (hsub : (B k).closedBall ⊆ (B l).closedBall) : False := by
      obtain ⟨y, hy⟩ := (surgeryBall_frontier_connected (B k)).nonempty
      exact hcloutside l (hfrontclosure k hy)
        (subset_interior_of_subset_of_disjoint_frontiers (hclosed k) hsub hkl
          ((hclosed k).frontier_subset hy))
    rcases closed_regions_nested_or_disjoint (hclosed i) (hclosed j)
        (surgeryBall_closedBall_connected (B i)).isPreconnected (hBout i)
        (surgeryBall_frontier_connected (B j)).isPreconnected (hdisjoint i j hij)
        p (hpB i) (hpB j) with h | h | h
    · exact h
    · exact (hnested i j (hdisjoint i j hij) h).elim
    · exact (hnested j i (hdisjoint i j hij).symm h).elim
  refine ⟨hsep, Subset.antisymm ?_ ?_⟩
  · intro y hy hunion
    obtain ⟨i, hi⟩ := mem_iUnion.mp hunion
    exact hUB i hy hi
  · have hc := surgeryBall_iUnion_complement_connected hA B hsep p hpB
    apply hc.isPreconnected.subset_of_closure_inter_subset hU
      ⟨p, by simpa only [mem_compl_iff, mem_iUnion, not_exists] using hpB, hp⟩
    rintro y ⟨hyclosure, hyout⟩
    by_contra hyU
    have hyfront : y ∈ frontier U := ⟨hyclosure, by simpa only [hU.interior_eq] using hyU⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfrontier ▸ hyfront)
    exact hyout (mem_iUnion.mpr ⟨i, (hclosed i).frontier_subset hi⟩)



theorem enclosing_ball_or_exact_complement_of_fillings
    (hA : IsPreconnected (univ : Set A.carrier))
    (hU : IsOpen U) (hconnected : IsConnected U)
    (B : ι → SurgeryBallEmbedding A)
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (frontier (B i).closedBall) (frontier (B j).closedBall))
    (hfrontier : frontier U = ⋃ i, frontier (B i).closedBall) :
    (∃ i, closure U ⊆ (B i).closedBall) ∨
      ((∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall) ∧
        U = (⋃ i, (B i).closedBall)ᶜ) := by
  classical
  obtain ⟨p, hp⟩ := hconnected.nonempty
  by_cases hinside : ∃ i, p ∈ (B i).closedBall
  · obtain ⟨i, hi⟩ := hinside
    have hclosed : IsClosed (B i).closedBall :=
      (surgeryBall_closedImage_compact (B i) 1 (by norm_num)).isClosed
    have havoid : Disjoint U (frontier (B i).closedBall) := by
      apply disjoint_left.mpr
      intro y hy hyf
      have h := hfrontier.symm ▸ mem_iUnion.mpr ⟨i, hyf⟩
      exact h.2 (hU.interior_eq.symm ▸ hy)
    rcases preconnected_subset_interior_or_compl hclosed hconnected.isPreconnected
        havoid with hin | hout
    · exact Or.inl ⟨i, closure_minimal (hin.trans interior_subset) hclosed⟩
    · exact (hout hp hi).elim
  · exact Or.inr (region_eq_complement_of_avoiding_fillings hA hU hconnected B
      hdisjoint hfrontier p hp (not_exists.mp hinside))

end PoincareConjecture.M38
