import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Clearance







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

private theorem tube_mem_retained_union (q : S1) {t : Real}
    (ht : t ∈ Ioo (-S.ε) S.ε) (hout : t ≤ -S.a ∨ S.a ≤ t) :
    S.T (q, t) ∈ S.eMinus '' closedBall (0 : E2) 1 ∪
      S.ePlus '' closedBall (0 : E2) 1 := by
  have hcover : S.T (q, t) ∈ S.eMinus '' closedBall (0 : E2) 1 ∪
      S.T '' (univ ×ˢ Icc (-S.a) S.a) ∪ S.ePlus '' closedBall (0 : E2) 1 := by
    rw [S.disk_slab_cover]
    exact mem_univ _
  rcases hcover with (hminus | ⟨⟨q', u⟩, ⟨_, hu⟩, heq⟩) | hplus
  · exact Or.inl hminus
  · have hsource : (q', u) ∈ S.T.source := by
      rw [S.tube_source]
      exact ⟨mem_univ _, by linarith [hu.1, S.a_lt_quarter_ε, S.a_pos],
        by linarith [hu.2, S.a_lt_quarter_ε, S.a_pos]⟩
    have heq' := S.T.injOn hsource (by rw [S.tube_source]; exact ⟨mem_univ _, ht⟩) heq
    have hut : u = t := congrArg Prod.snd heq'
    rcases hout with htminus | htplus
    · have htedge : t = -S.a := by linarith [hu.1]
      left
      apply image_mono sphere_subset_closedBall
      rw [S.eMinus_boundary, htedge]
      exact mem_range_self q
    · have htedge : t = S.a := by linarith [hu.2]
      right
      apply image_mono sphere_subset_closedBall
      rw [S.ePlus_boundary, htedge]
      exact mem_range_self q
  · exact Or.inr hplus

private theorem retained_of_preconnected {K : Set S2}
    (hK : IsPreconnected K)
    (hsub : K ⊆ S.eMinus '' closedBall 0 1 ∪ S.ePlus '' closedBall 0 1) :
    ¬ ((K ∩ (S.eMinus '' closedBall 0 1)).Nonempty ∧
      (K ∩ (S.ePlus '' closedBall 0 1)).Nonempty) := by
  rintro ⟨hm, hp⟩
  have hcm := (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
    (S.eMinus.continuousOn.mono S.eMinus_source)
  have hcp := (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
    (S.ePlus.continuousOn.mono S.ePlus_source)
  obtain ⟨x, _, hx⟩ := isPreconnected_closed_iff.mp hK _ _
    hcm.isClosed hcp.isClosed hsub hm hp
  exact disjoint_left.mp S.retained_disjoint hx.1 hx.2


theorem tube_mem_retainedMinus (q : S1) {t : Real}
    (ht : -S.ε < t) (hta : t ≤ -S.a) :
    S.T (q, t) ∈ S.eMinus '' closedBall (0 : E2) 1 := by
  let K := (fun u : Real => S.T (q, u)) '' Icc t (-S.a)
  have hs : MapsTo (fun u : Real => (q, u)) (Icc t (-S.a)) S.T.source := by
    intro u hu
    rw [S.tube_source]
    exact ⟨mem_univ _, ht.trans_le hu.1,
      by linarith [hu.2, S.a_pos, S.ε_pos]⟩
  have hK : IsPreconnected K := isPreconnected_Icc.image _
    (S.T.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hs)
  have hsub : K ⊆ S.eMinus '' closedBall 0 1 ∪ S.ePlus '' closedBall 0 1 := by
    rintro y ⟨u, hu, rfl⟩
    exact S.tube_mem_retained_union q (by simpa [S.tube_source] using hs hu)
      (Or.inl hu.2)
  have hm : (K ∩ (S.eMinus '' closedBall 0 1)).Nonempty := by
    refine ⟨S.T (q, -S.a), ⟨-S.a, ⟨hta, le_rfl⟩, rfl⟩, ?_⟩
    apply image_mono sphere_subset_closedBall
    rw [S.eMinus_boundary]
    exact mem_range_self q
  have htk : S.T (q, t) ∈ K := ⟨t, ⟨le_rfl, hta⟩, rfl⟩
  rcases hsub htk with hm' | hp'
  · exact hm'
  · exact False.elim (S.retained_of_preconnected hK hsub ⟨hm, ⟨_, htk, hp'⟩⟩)


theorem tube_mem_retainedPlus (q : S1) {t : Real}
    (ht : t < S.ε) (hta : S.a ≤ t) :
    S.T (q, t) ∈ S.ePlus '' closedBall (0 : E2) 1 := by
  let K := (fun u : Real => S.T (q, u)) '' Icc S.a t
  have hs : MapsTo (fun u : Real => (q, u)) (Icc S.a t) S.T.source := by
    intro u hu
    rw [S.tube_source]
    exact ⟨mem_univ _, by linarith [hu.1, S.a_pos, S.ε_pos], hu.2.trans_lt ht⟩
  have hK : IsPreconnected K := isPreconnected_Icc.image _
    (S.T.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hs)
  have hsub : K ⊆ S.eMinus '' closedBall 0 1 ∪ S.ePlus '' closedBall 0 1 := by
    rintro y ⟨u, hu, rfl⟩
    exact S.tube_mem_retained_union q (by simpa [S.tube_source] using hs hu)
      (Or.inr hu.1)
  have hp : (K ∩ (S.ePlus '' closedBall 0 1)).Nonempty := by
    refine ⟨S.T (q, S.a), ⟨S.a, ⟨le_rfl, hta⟩, rfl⟩, ?_⟩
    apply image_mono sphere_subset_closedBall
    rw [S.ePlus_boundary]
    exact mem_range_self q
  have htk : S.T (q, t) ∈ K := ⟨t, ⟨hta, le_rfl⟩, rfl⟩
  rcases hsub htk with hm' | hp'
  · exact False.elim (S.retained_of_preconnected hK hsub ⟨⟨_, htk, hm'⟩, hp⟩)
  · exact hp'

end Poincare.Manifold.Schoenflies.SphereSurgeryStep

end

end M38Schoenflies
