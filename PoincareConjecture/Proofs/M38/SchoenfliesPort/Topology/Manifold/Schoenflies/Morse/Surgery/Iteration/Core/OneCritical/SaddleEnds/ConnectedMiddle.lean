import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Decomposition







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private theorem isPreconnected_middle_of_disjoint_closed_ends
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {C K : Set X} {E : ι → Set X}
    (hC : IsPreconnected C) (hK : IsClosed K) (hE : ∀ i, IsClosed (E i))
    (hpair : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : C = K ∪ ⋃ i, E i)
    (hattach : ∀ i, IsConnected (K ∩ E i)) : IsPreconnected K := by
  classical
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hK]
  intro U V hU hV hUV hdis
  let L : Set ι := {i | K ∩ E i ⊆ U}
  let R : Set ι := {i | K ∩ E i ⊆ V}
  let U' := (K ∩ U) ∪ ⋃ i ∈ L, E i
  let V' := (K ∩ V) ∪ ⋃ i ∈ R, E i
  have hside (i : ι) : i ∈ L ∨ i ∈ R :=
    isPreconnected_iff_subset_of_disjoint_closed.mp (hattach i).isPreconnected U V hU hV
      (inter_subset_left.trans hUV) (by rw [hdis.inter_eq, inter_empty])
  have hU' : IsClosed U' := (hK.inter hU).union (L.toFinite.isClosed_biUnion (fun i _ => hE i))
  have hV' : IsClosed V' := (hK.inter hV).union (R.toFinite.isClosed_biUnion (fun i _ => hE i))
  have hdis' : Disjoint U' V' := by
    apply Set.disjoint_left.mpr
    rintro x (hxU | hxU) (hxV | hxV)
    · exact Set.disjoint_left.mp hdis hxU.2 hxV.2
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxV
      exact Set.disjoint_left.mp hdis hxU.2 (hi ⟨hxU.1, hxi⟩)
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
      exact Set.disjoint_left.mp hdis (hi ⟨hxV.1, hxi⟩) hxV.2
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxV
      by_cases hij : i = j
      · subst j
        obtain ⟨y, hy⟩ := (hattach i).nonempty
        exact Set.disjoint_left.mp hdis (hi hy) (hj hy)
      · exact Set.disjoint_left.mp (hpair hij) hxi hxj
  have hcover' : C ⊆ U' ∪ V' := by
    rw [hcover]
    rintro x (hx | hx)
    · rcases hUV hx with hxU | hxV
      · exact Or.inl (Or.inl ⟨hx, hxU⟩)
      · exact Or.inr (Or.inl ⟨hx, hxV⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rcases hside i with hiL | hiR
      · exact Or.inl (Or.inr (mem_iUnion_of_mem i (mem_iUnion_of_mem hiL hi)))
      · exact Or.inr (Or.inr (mem_iUnion_of_mem i (mem_iUnion_of_mem hiR hi)))
  have hKsub : K ⊆ C := hcover ▸ subset_union_left
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hC U' V' hU' hV' hcover'
      (by rw [hdis'.inter_eq, inter_empty]) with hleft | hright
  · left
    intro x hx
    rcases hleft (hKsub hx) with hxU | hxE
    · exact hxU.2
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxE
      exact hi ⟨hx, hxi⟩
  · right
    intro x hx
    rcases hright (hKsub hx) with hxV | hxE
    · exact hxV.2
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxE
      exact hi ⟨hx, hxi⟩

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private instance : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
  (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

private theorem isConnected_upper_strip_boundary
    (F : OpenPartialHomeomorph (S1 × Real) S2) {h : S2 → Real} {a b c : Real}
    (hab : a ≤ b) (hbc : b ≤ c) (hsub : univ ×ˢ Icc a b ⊆ F.source)
    (hheight : ∀ q t, t ∈ Icc a b → h (F (q, t)) = t) :
    IsConnected ((F '' (univ ×ˢ Icc a b)) ∩ h ⁻¹' Icc b c) := by
  have heq : (F '' (univ ×ˢ Icc a b)) ∩ h ⁻¹' Icc b c =
      range (fun q : S1 => F (q, b)) := by
    ext p
    constructor
    · rintro ⟨⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, hp⟩
      have hht := hheight q t ht
      have htb : t = b := le_antisymm ht.2 (by simpa only [hht] using hp.1)
      exact ⟨q, by rw [htb]⟩
    · rintro ⟨q, rfl⟩
      refine ⟨mem_image_of_mem F ⟨mem_univ _, hab, le_rfl⟩, ?_⟩
      change h (F (q, b)) ∈ Icc b c
      rw [hheight q b ⟨hab, le_rfl⟩]
      exact ⟨le_rfl, hbc⟩
  rw [heq]
  have hcont : Continuous (fun q : S1 => F (q, b)) :=
    F.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun q => hsub ⟨mem_univ _, hab, le_rfl⟩)
  simpa only [image_univ] using isConnected_univ.image _ hcont.continuousOn

private theorem isConnected_lower_strip_boundary
    (F : OpenPartialHomeomorph (S1 × Real) S2) {h : S2 → Real} {a b c : Real}
    (hab : a ≤ b) (hbc : b ≤ c) (hsub : univ ×ˢ Icc b c ⊆ F.source)
    (hheight : ∀ q t, t ∈ Icc b c → h (F (q, t)) = t) :
    IsConnected ((F '' (univ ×ˢ Icc b c)) ∩ h ⁻¹' Icc a b) := by
  have heq : (F '' (univ ×ˢ Icc b c)) ∩ h ⁻¹' Icc a b =
      range (fun q : S1 => F (q, b)) := by
    ext p
    constructor
    · rintro ⟨⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, hp⟩
      have hht := hheight q t ht
      have htb : t = b := le_antisymm (by simpa only [hht] using hp.2) ht.1
      exact ⟨q, by rw [htb]⟩
    · rintro ⟨q, rfl⟩
      refine ⟨mem_image_of_mem F ⟨mem_univ _, le_rfl, hbc⟩, ?_⟩
      change h (F (q, b)) ∈ Icc a b
      rw [hheight q b ⟨le_rfl, hbc⟩]
      exact ⟨hab, le_rfl⟩
  rw [heq]
  have hcont : Continuous (fun q : S1 => F (q, b)) :=
    F.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun q => hsub ⟨mem_univ _, le_rfl, hbc⟩)
  simpa only [image_univ] using isConnected_univ.image _ hcont.continuousOn

namespace SphereSurgeryCoreCap.AnnularEndFamily

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

theorem cap_center_bounds (A : AnnularEndFamily v g B C)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ A.caps) :
    D.center ∈ Ioo A.lowerBound A.upperBound := by
  obtain ⟨p, hp⟩ := D.isConnected_boundary.nonempty
  have hpC := ((core_inter_closed_disk A.caps A.caps_disjoint A.core_complement D hD).superset hp).1
  have hh := ((A.height_germ p hpC).eq_of_nhds).trans (D.height_eq_on_boundary p hp)
  exact hh ▸ A.core_height_bounds p hpC

theorem endRegion_isCompact (A : AnnularEndFamily v g B C) (i : A.EndIndex) :
    IsCompact (A.endRegion i) := by
  rcases i with D | D
  · let F := A.lower D.1.1 D.1.2 D.2
    have hsource : univ ×ˢ Icc D.1.1.center A.lowerCut ⊆ F.chart.source := by
      rintro ⟨q, t⟩ ⟨_, ht⟩
      rw [F.source]
      exact ⟨mem_univ _, by linarith [(A.cap_center_bounds D.1.1 D.1.2).1, F.delta_pos, ht.1],
        by linarith [F.delta_pos, ht.2]⟩
    exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (F.chart.continuousOn.mono hsource)
  · let F := A.upper D.1.1 D.1.2 D.2
    change IsCompact F.region
    rw [F.region_eq_image]
    have hsource : univ ×ˢ Icc A.upperCut D.1.1.center ⊆ F.chart.source := by
      rintro ⟨q, t⟩ ⟨_, ht⟩
      rw [F.source]
      exact ⟨mem_univ _, by linarith [F.reflected.delta_pos, ht.1],
        by linarith [(A.cap_center_bounds D.1.1 D.1.2).2, F.reflected.delta_pos, ht.2]⟩
    exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (F.chart.continuousOn.mono hsource)

theorem isConnected_middle_inter_end (A : AnnularEndFamily v g B C) (i : A.EndIndex) :
    IsConnected (A.middleRegion ∩ A.endRegion i) := by
  have heq : A.middleRegion ∩ A.endRegion i =
      A.endRegion i ∩ A.height ⁻¹' Icc A.lowerCut A.upperCut := by
    ext p
    exact ⟨fun hp => ⟨hp.2, hp.1.2⟩,
      fun hp => ⟨⟨A.endRegion_subset_core i hp.1, hp.2⟩, hp.1⟩⟩
  rw [heq]
  rcases i with D | D
  · let F := A.lower D.1.1 D.1.2 D.2
    apply isConnected_upper_strip_boundary F.chart D.2.le A.cuts_lt.le
    · rintro ⟨q, t⟩ ⟨_, ht⟩
      rw [F.source]
      exact ⟨mem_univ _, by linarith [(A.cap_center_bounds D.1.1 D.1.2).1, F.delta_pos, ht.1],
        by linarith [F.delta_pos, ht.2]⟩
    · intro q t ht
      have hpC := F.retained (mem_image_of_mem F.chart
        (show (q, t) ∈ univ ×ˢ Icc D.1.1.center A.lowerCut from ⟨mem_univ _, ht⟩))
      exact ((A.height_germ _ hpC).eq_of_nhds).trans (F.actual_height q t ht)
  · let F := A.upper D.1.1 D.1.2 D.2
    change IsConnected (F.region ∩ _)
    rw [F.region_eq_image]
    apply isConnected_lower_strip_boundary F.chart A.cuts_lt.le D.2.le
    · rintro ⟨q, t⟩ ⟨_, ht⟩
      rw [F.source]
      exact ⟨mem_univ _, by linarith [F.reflected.delta_pos, ht.1],
        by linarith [(A.cap_center_bounds D.1.1 D.1.2).2, F.reflected.delta_pos, ht.2]⟩
    · intro q t ht
      have hpR : F.chart (q, t) ∈ F.region := F.region_eq_image.superset
        (mem_image_of_mem _ ⟨mem_univ _, ht⟩)
      exact ((A.height_germ _ (F.retained hpR)).eq_of_nhds).trans (F.actual_height q t ht)



theorem isPreconnected_middleRegion (A : AnnularEndFamily v g B C)
    (hC : IsPreconnected C) (hclosed : IsClosed C) : IsPreconnected A.middleRegion := by
  apply isPreconnected_middle_of_disjoint_closed_ends hC
    (hclosed.inter (isClosed_Icc.preimage A.height_smooth.continuous))
    (fun i => (A.endRegion_isCompact i).isClosed) A.pairwise_disjoint
    A.core_eq_middle_union_ends A.isConnected_middle_inter_end

end SphereSurgeryCoreCap.AnnularEndFamily

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
