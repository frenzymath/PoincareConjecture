import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

theorem subset_of_preconnected_closed_union
    {X : Type*} [TopologicalSpace X] {L R J : Set X}
    (hL : IsClosed L) (hR : IsClosed R) (hLR : Disjoint L R)
    (hJ : IsPreconnected J) (hsub : J ⊆ L ∪ R) (hJL : (J ∩ L).Nonempty) : J ⊆ L := by
  intro x hx
  rcases hsub hx with hxL | hxR
  · exact hxL
  · obtain ⟨z, _, hzL, hzR⟩ :=
      isPreconnected_closed_iff.mp hJ L R hL hR hsub hJL ⟨x, hx, hxR⟩
    exact (Set.disjoint_left.mp hLR hzL hzR).elim

theorem disjoint_closed_components_unique
    {X : Type*} [TopologicalSpace X] {L R J K : Set X}
    (hL : IsClosed L) (hR : IsClosed R) (hLR : Disjoint L R)
    (hJ : IsPreconnected J) (hK : IsPreconnected K) (hcover : J ∪ K = L ∪ R)
    (hJL : (J ∩ L).Nonempty) (hKR : (K ∩ R).Nonempty) : J = L ∧ K = R := by
  have hJLsub := subset_of_preconnected_closed_union hL hR hLR hJ
    (subset_union_left.trans hcover.subset) hJL
  have hKRsub := subset_of_preconnected_closed_union hR hL hLR.symm hK
    (by simpa only [union_comm R L] using subset_union_right.trans hcover.subset) hKR
  constructor
  · apply Subset.antisymm hJLsub
    intro x hxL
    rcases hcover.symm.subset (Or.inl hxL) with hxJ | hxK
    · exact hxJ
    · exact (Set.disjoint_left.mp hLR hxL (hKRsub hxK)).elim
  · apply Subset.antisymm hKRsub
    intro x hxR
    rcases hcover.symm.subset (Or.inr hxR) with hxJ | hxK
    · exact (Set.disjoint_left.mp hLR (hJLsub hxJ) hxR).elim
    · exact hxK

theorem disjoint_finitePL_intervals_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L R J K PL PR PJ PK : Set E}
    (hL : IsFinitePLBallPair ℝ L PL) (hR : IsFinitePLBallPair ℝ R PR)
    (hJ : IsFinitePLBallPair ℝ J PJ) (hK : IsFinitePLBallPair ℝ K PK)
    (hLR : Disjoint L R) (hcover : J ∪ K = L ∪ R)
    (hJL : (J ∩ L).Nonempty) (hKR : (K ∩ R).Nonempty) : J = L ∧ K = R :=
  disjoint_closed_components_unique hL.isCompact.isClosed hR.isCompact.isClosed hLR
    hJ.isConnected.isPreconnected hK.isConnected.isPreconnected hcover hJL hKR

theorem isPreconnected_of_interval_chart
    {X : Type*} [TopologicalSpace X] {J : Set X}
    (q : Icc (0 : ℝ) 1 ≃ₜ J) : IsPreconnected J := by
  have h := isPreconnected_range (continuous_subtype_val.comp q.continuous)
  have hrange : range (fun t : Icc (0 : ℝ) 1 ↦ (q t : X)) = J := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (q t).property
    · intro hx
      obtain ⟨t, ht⟩ := q.surjective ⟨x, hx⟩
      exact ⟨t, congrArg Subtype.val ht⟩
  simpa only [Function.comp_def, hrange] using h

theorem disjoint_interval_charts_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L R J K PL PR : Set E} {a b : E}
    (hL : IsFinitePLBallPair ℝ L PL) (hR : IsFinitePLBallPair ℝ R PR)
    (hLR : Disjoint L R) (hcover : J ∪ K = L ∪ R)
    (qJ : Icc (0 : ℝ) 1 ≃ₜ J) (qK : Icc (0 : ℝ) 1 ≃ₜ K)
    (hqJ : (qJ (0 : unitInterval) : E) = a)
    (hqK : (qK (1 : unitInterval) : E) = b)
    (ha : a ∈ L) (hb : b ∈ R) : J = L ∧ K = R := by
  apply disjoint_closed_components_unique hL.isCompact.isClosed hR.isCompact.isClosed hLR
    (isPreconnected_of_interval_chart qJ) (isPreconnected_of_interval_chart qK) hcover
  · exact ⟨a, hqJ ▸ (qJ 0).property, ha⟩
  · exact ⟨b, hqK ▸ (qK 1).property, hb⟩

end PoincareConjecture.M76.Dehn
