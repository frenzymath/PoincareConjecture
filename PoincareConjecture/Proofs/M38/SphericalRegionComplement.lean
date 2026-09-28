import PoincareConjecture.Proofs.M38.SphericalSphereFilling
import PoincareConjecture.Proofs.M38.FiniteSphereNesting
import PoincareConjecture.Proofs.M38.FiniteBallComplement

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_spherical_region_complement
    {ι : Type*} [Finite ι] {U : Set sphereCarrier.{u}.carrier}
    (hU : IsOpen U) (hconnected : IsConnected U)
    (f : ι → UnitTwoSphere → sphereCarrier.{u}.carrier)
    (hf : ∀ i, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (range (f i)) (range (f j)))
    (hfrontier : frontier U = ⋃ i, range (f i)) :
    ∃ B : ι → SurgeryBallEmbedding sphereCarrier.{u},
      (∀ i, frontier (B i).closedBall = range (f i)) ∧
      (∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall) ∧
      U = (⋃ i, (B i).closedBall)ᶜ := by
  classical
  obtain ⟨p, hp⟩ := hconnected.nonempty
  have hUf (i : ι) : Disjoint U (range (f i)) := by
    apply disjoint_left.mpr
    intro y hy hyf
    have hyfront : y ∈ frontier U := hfrontier.symm ▸ mem_iUnion.mpr ⟨i, hyf⟩
    exact hyfront.2 (hU.interior_eq.symm ▸ hy)
  have hpf (i : ι) : p ∉ range (f i) := fun h => disjoint_left.mp (hUf i) hp h
  choose B hB hpB using fun i => exists_surgerySphereBall_avoiding_point (f i) (hf i) p (hpf i)
  have hclosed (i) : IsClosed (B i).closedBall :=
    (surgeryBall_closedImage_compact (B i) 1 (by norm_num)).isClosed
  have hUB (i) : U ⊆ (B i).closedBallᶜ := by
    rcases preconnected_subset_interior_or_compl (hclosed i) hconnected.isPreconnected
        ((hB i).symm ▸ hUf i) with hin | hout
    · exact (hpB i (interior_subset (hin hp))).elim
    · exact hout
  have hfrontclosure (i) : frontier (B i).closedBall ⊆ closure U := by
    intro y hy
    exact frontier_subset_closure (hfrontier.symm ▸ mem_iUnion.mpr ⟨i, hB i ▸ hy⟩)
  have hcloutside (i) : closure U ⊆ (interior (B i).closedBall)ᶜ :=
    closure_minimal (fun y hy h => hUB i hy (interior_subset h)) isOpen_interior.isClosed_compl
  have hsep (i j : ι) (hij : i ≠ j) : Disjoint (B i).closedBall (B j).closedBall := by
    have hfront : Disjoint (frontier (B i).closedBall) (frontier (B j).closedBall) := by
      rw [hB, hB]
      exact hdisjoint i j hij
    have hnested (k l : ι)
        (hkl : Disjoint (frontier (B k).closedBall) (frontier (B l).closedBall))
        (hsub : (B k).closedBall ⊆ (B l).closedBall) : False := by
      obtain ⟨y, hy⟩ := (surgeryBall_frontier_connected (B k)).nonempty
      exact hcloutside l (hfrontclosure k hy)
        (subset_interior_of_subset_of_disjoint_frontiers (hclosed k) hsub hkl
          ((hclosed k).frontier_subset hy))
    rcases sphereBalls_nested_or_disjoint (B i) (B j) hfront p (hpB i) (hpB j) with
      h | h | h
    · exact h
    · exact (hnested i j hfront h).elim
    · exact (hnested j i hfront.symm h).elim
  refine ⟨B, hB, hsep, Subset.antisymm ?_ ?_⟩
  · intro y hy hunion
    obtain ⟨i, hi⟩ := mem_iUnion.mp hunion
    exact hUB i hy hi
  · let : ConnectedSpace UnitThreeSphere := isConnected_iff_connectedSpace.mp
      (isConnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank (by simp))
        (0 : EuclideanSpace ℝ (Fin 4)) zero_le_one)
    let : ConnectedSpace sphereCarrier.{u}.carrier :=
      (Homeomorph.ulift : sphereCarrier.{u}.carrier ≃ₜ UnitThreeSphere).connectedSpace_iff.mpr
        inferInstance
    have hc := surgeryBall_iUnion_complement_connected
      (show IsPreconnected (univ : Set sphereCarrier.{u}.carrier) from isPreconnected_univ)
      B hsep p hpB
    apply hc.isPreconnected.subset_of_closure_inter_subset hU
      ⟨p, by simpa only [mem_compl_iff, mem_iUnion, not_exists] using hpB, hp⟩
    rintro y ⟨hyclosure, hyout⟩
    by_contra hyU
    have hyfront : y ∈ frontier U := ⟨hyclosure, by simpa only [hU.interior_eq] using hyU⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfrontier ▸ hyfront)
    exact hyout (mem_iUnion.mpr ⟨i, (hclosed i).frontier_subset ((hB i).symm ▸ hi)⟩)

end PoincareConjecture.M38
