import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCollarCore
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapFaces
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerBandChords

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

namespace M64IntrinsicThreeArcCaps

variable {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
  {T : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
  (C : M64IntrinsicThreeArcCaps gamma sigma T S U)

theorem first_axis_mem (e : Bool) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (C.radius e)) :
    C.chart e (s, 0) ∈ C.carrier e :=
  ((C.frontier_contact e).symm.subset (Or.inl ⟨s, hs, (C.first_axis e s).symm⟩)).1

theorem second_axis_mem (e : Bool) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (C.radius e)) :
    C.chart e (0, s) ∈ C.carrier e :=
  ((C.frontier_contact e).symm.subset (Or.inr ⟨s, hs, (C.second_axis e s).symm⟩)).1

theorem disjoint_of_ne (e f : Bool) (hef : e ≠ f) : Disjoint (C.carrier e) (C.carrier f) := by
  cases e <;> cases f
  · exact (hef rfl).elim
  · exact C.separated
  · exact C.separated.symm
  · exact (hef rfl).elim

end M64IntrinsicThreeArcCaps

private theorem lower_subset_carrier (B : M64IntrinsicLinearBandData) :
    B.band.lowerArc ⊆ B.band.carrier :=
  fun _ hp => B.band.isClosed_carrier.frontier_subset
    (B.band.outer_boundaries_subset_frontier (Or.inl (Or.inl (Or.inl hp))))

private theorem optional_subset (p : Prop) [Decidable p] (A : Set AnnulusCoordinates) :
    (if p then A else ∅) ⊆ A := by
  split_ifs
  · exact Subset.rfl
  · exact empty_subset _

private theorem lower_cut_base (B : M64IntrinsicLinearBandData) (right : Bool)
    {p : AnnulusCoordinates}
    (hp : p ∈ if right then B.band.rightCut else B.band.leftCut)
    (hlower : p ∈ B.band.lowerArc) : p = (B.band.endpointEdge right).map 0 := by
  rw [← B.band.endpointEdge_image] at hp
  obtain ⟨t, ht, heq⟩ := hp
  have ht0 := (m64Intrinsic_band_endpoint_mem_lower_iff B.band right ht).mp
    (heq.symm ▸ hlower)
  simpa only [ht0] using heq.symm

namespace M64IntrinsicThreeArcCollar

variable {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
  {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
  (D : M64IntrinsicThreeArcCollar C b)

theorem cap_band_outer (e : Bool) (i : D.BandIndex) :
    C.carrier e ∩ (D.bandData i).band.carrier ⊆
      (D.bandData i).band.leftCut ∪ (D.bandData i).band.rightCut := by
  intro p hp
  rcases i with ⟨f, i⟩ | (f | i)
  · by_cases hef : e = f
    · subst f
      have h := (D.joined.cap_contact e i).subset hp
      cases e
      · exact Or.inl (optional_subset _ _ h)
      · exact Or.inr (optional_subset _ _ h)
    · have he : e = !f := by
        cases e <;> cases f
        · exact (hef rfl).elim
        · rfl
        · rfl
        · exact (hef rfl).elim
      subst e
      exact (disjoint_left.mp (D.joined.opposite_cap f i) hp.1 hp.2).elim
  · exact (disjoint_left.mp (D.joined.caps_patch_disjoint e f) hp.1 hp.2).elim
  · have hc : p ∈ C.carrier false ∪ C.carrier true := by
      cases e
      · exact Or.inl hp.1
      · exact Or.inr hp.1
    have h := (D.cap_contact i).subset ⟨hc, hp.2⟩
    rcases h with h | h
    · exact Or.inl (optional_subset _ _ h)
    · exact Or.inr (optional_subset _ _ h)

theorem cap_band_lower_tips (e : Bool) (i : D.BandIndex) :
    C.carrier e ∩ (D.bandData i).band.lowerArc ⊆
      {C.chart e (C.radius e, 0), C.chart e (0, C.radius e)} := by
  intro p hp
  have hpband := lower_subset_carrier (D.bandData i) hp.2
  have hown (f : Bool) (h : p = C.chart f (0, C.radius f)) :
      p = C.chart e (0, C.radius e) := by
    by_cases hef : e = f
    · subst f
      exact h
    · exact (disjoint_left.mp (C.disjoint_of_ne e f hef) hp.1
        (h.symm ▸ C.second_axis_mem f (C.radius f) ⟨(C.radius_pos f).le, le_rfl⟩)).elim
  rcases i with ⟨f, i⟩ | (f | i)
  · by_cases hef : e = f
    · subst f
      have h := (D.joined.cap_contact e i).subset ⟨hp.1, hpband⟩
      cases e
      · change p ∈ (if (D.joined.chain false).cut i.castSucc = C.radius false
          then ((D.joined.chain false).band i).leftCut else ∅) at h
        by_cases hcut : (D.joined.chain false).cut i.castSucc = C.radius false
        · rw [if_pos hcut] at h
          have hb := lower_cut_base (.ofChain (D.joined.chain false) i) false h hp.2
          change p = (((D.joined.chain false).band i).endpointEdge false).map 0 at hb
          rw [(D.joined.chain false).endpoint_zero] at hb
          change p = gamma false ((D.joined.chain false).cut i.castSucc) at hb
          rw [hcut] at hb
          exact Or.inl (hb.trans (C.first_axis false (C.radius false)).symm)
        · rw [if_neg hcut] at h
          exact h.elim
      · change p ∈ (if (D.joined.chain true).cut i.succ = T true - C.radius true
          then ((D.joined.chain true).band i).rightCut else ∅) at h
        by_cases hcut : (D.joined.chain true).cut i.succ = T true - C.radius true
        · rw [if_pos hcut] at h
          have hb := lower_cut_base (.ofChain (D.joined.chain true) i) true h hp.2
          change p = (((D.joined.chain true).band i).endpointEdge true).map 0 at hb
          rw [(D.joined.chain true).endpoint_zero] at hb
          change p = gamma true ((D.joined.chain true).cut i.succ) at hb
          rw [hcut] at hb
          exact Or.inl (hb.trans (C.first_axis true (C.radius true)).symm)
        · rw [if_neg hcut] at h
          exact h.elim
    · have he : e = !f := by
        cases e <;> cases f
        · exact (hef rfl).elim
        · rfl
        · rfl
        · exact (hef rfl).elim
      subst e
      exact (disjoint_left.mp (D.joined.opposite_cap f i) hp.1 hpband).elim
  · exact (disjoint_left.mp (D.joined.caps_patch_disjoint e f) hp.1 hpband).elim
  · have hc : p ∈ C.carrier false ∪ C.carrier true := by
      cases e
      · exact Or.inl hp.1
      · exact Or.inr hp.1
    have h := (D.cap_contact i).subset ⟨hc, hpband⟩
    rcases h with h | h
    · by_cases hcut : D.third.cut i.castSucc = C.radius (if D.reversed then true else false)
      · rw [if_pos hcut] at h
        have hb := lower_cut_base (.ofChain D.third i) false h hp.2
        change p = ((D.third.band i).endpointEdge false).map 0 at hb
        rw [D.third.endpoint_zero] at hb
        change p = sigma (if D.reversed then S - D.third.cut i.castSucc
          else D.third.cut i.castSucc) at hb
        rw [hcut] at hb
        apply Or.inr
        apply hown (if D.reversed then true else false)
        apply hb.trans
        rw [C.second_axis]
        cases D.reversed <;> rfl
      · rw [if_neg hcut] at h
        exact h.elim
    · by_cases hcut : D.third.cut i.succ = S - C.radius (if D.reversed then false else true)
      · rw [if_pos hcut] at h
        have hb := lower_cut_base (.ofChain D.third i) true h hp.2
        change p = ((D.third.band i).endpointEdge true).map 0 at hb
        rw [D.third.endpoint_zero] at hb
        change p = sigma (if D.reversed then S - D.third.cut i.succ
          else D.third.cut i.succ) at hb
        rw [hcut] at hb
        apply Or.inr
        apply hown (if D.reversed then false else true)
        apply hb.trans
        rw [C.second_axis]
        cases D.reversed <;> simp only [Bool.false_eq_true, if_false, if_true, sub_sub_cancel]
      · rw [if_neg hcut] at h
        exact h.elim

theorem band_off_lower (i : D.BandIndex) :
    (D.bandData i).band.carrier \ (D.bandData i).band.lowerArc ⊆ U := by
  rcases i with ⟨e, i⟩ | (e | i)
  · exact (D.joined.chain e).off_lower i
  · exact D.joined.patch.off_lower e
  · exact D.third.off_lower i

theorem cap_face_band_chord (hU : IsOpen U) (A : M64IntrinsicThreeArcCapFaces C)
    (e : Bool) (j : Bool × Bool)
    (hj : if C.positive e then j = (true, true) else j ≠ (true, true)) (i : D.BandIndex) :
    (A.face e j).carrier ∩ (D.bandData i).band.carrier ⊆
      ((A.face e j).boundary 0).map '' Icc (0 : ℝ) 1 := by
  apply m64Intrinsic_retained_corner_band_inter_subset_chord (C.chart e) (C.radius_pos e)
    (A.face e) (C.positive e) ?_ (A.sector e) (A.second e) (A.first e) (A.chord e)
    (fun j => ⟨A.coordinates e j, A.basis e j, A.smooth e j, A.inverse_smooth e j,
      A.source e j, A.carrier e j, A.boundary e j⟩)
    (D.bandData i).band (disjoint_frontier_iff_isOpen.mpr hU).symm (D.band_off_lower i)
    (C.axes_subset_frontier e) ?_ ?_ j hj
  · simpa only [sectorParameterEquiv_apply, if_true, Prod.fst_zero, Prod.snd_zero,
      zero_add, one_mul, add_zero] using
      C.axes_source e (true, true) (C.radius e) ⟨(C.radius_pos e).le, le_rfl⟩
  · rintro p ⟨(⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩), hp⟩
    · exact D.cap_band_lower_tips e i
        ⟨C.second_axis_mem e _ ⟨mul_nonneg ht.1 (C.radius_pos e).le,
          mul_le_of_le_one_left (C.radius_pos e).le ht.2⟩, hp⟩
    · exact D.cap_band_lower_tips e i
        ⟨C.first_axis_mem e _ ⟨mul_nonneg ht.1 (C.radius_pos e).le,
          mul_le_of_le_one_left (C.radius_pos e).le ht.2⟩, hp⟩
  · rw [A.occupied_union]
    exact D.cap_band_outer e i

end M64IntrinsicThreeArcCollar

end PoincareConjecture
