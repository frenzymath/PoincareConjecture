import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerArcCapContacts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCapFaces

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture.M64IntrinsicTriangleCollar

variable {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicTriangleCaps base alpha beta D A B U} (P : M64IntrinsicTriangleCollar C)

theorem cap_band_outer (j : Fin 3) (i : P.BandIndex) :
    C.carrier j ∩ (P.bandData i).band.carrier ⊆
      (P.bandData i).band.leftCut ∪ (P.bandData i).band.rightCut := by
  rcases i with i | (i | i)
  · fin_cases j
    · exact P.baseArc.cap_band_outer 0 (Or.inl rfl) i
    · exact P.baseArc.cap_band_outer 1 (Or.inr rfl) i
    · intro p hp
      exact (disjoint_left.mp P.base_opposite (mem_iUnion.mpr ⟨i, hp.2⟩) hp.1).elim
  · fin_cases j
    · exact P.firstSide.cap_band_outer 0 (Or.inl rfl) i
    · intro p hp
      exact (disjoint_left.mp P.first_opposite (mem_iUnion.mpr ⟨i, hp.2⟩) hp.1).elim
    · exact P.firstSide.cap_band_outer 2 (Or.inr rfl) i
  · fin_cases j
    · intro p hp
      exact (disjoint_left.mp P.second_opposite (mem_iUnion.mpr ⟨i, hp.2⟩) hp.1).elim
    · exact P.secondSide.cap_band_outer 1 (Or.inl rfl) i
    · exact P.secondSide.cap_band_outer 2 (Or.inr rfl) i

theorem cap_band_lower_tips (j : Fin 3) (i : P.BandIndex) :
    C.carrier j ∩ (P.bandData i).band.lowerArc ⊆
      {C.chart j (C.radius j, 0), C.chart j (0, C.radius j)} := by
  have hbase (e : Bool) : base (if e then D - C.radius 1 else C.radius 0) ∈
      ({C.chart (if e then 1 else 0) (C.radius (if e then 1 else 0), 0),
        C.chart (if e then 1 else 0) (0, C.radius (if e then 1 else 0))} :
          Set AnnulusCoordinates) := by
    cases e
    · exact Or.inl (C.first_axis 0 (C.radius 0)).symm
    · exact Or.inl (C.first_axis 1 (C.radius 1)).symm
  have halpha (e : Bool) : alpha (if e then A - C.radius 2 else C.radius 0) ∈
      ({C.chart (if e then 2 else 0) (C.radius (if e then 2 else 0), 0),
        C.chart (if e then 2 else 0) (0, C.radius (if e then 2 else 0))} :
          Set AnnulusCoordinates) := by
    cases e
    · exact Or.inr (C.second_axis 0 (C.radius 0)).symm
    · exact Or.inl (C.first_axis 2 (C.radius 2)).symm
  have hbeta (e : Bool) : beta (if e then B - C.radius 2 else C.radius 1) ∈
      ({C.chart (if e then 2 else 1) (C.radius (if e then 2 else 1), 0),
        C.chart (if e then 2 else 1) (0, C.radius (if e then 2 else 1))} :
          Set AnnulusCoordinates) := by
    cases e
    · exact Or.inr (C.second_axis 1 (C.radius 1)).symm
    · exact Or.inr (C.second_axis 2 (C.radius 2)).symm
  have hbase' (j : Fin 3) (hj : j = 0 ∨ j = 1) (i : Fin P.baseArc.chain.count) :=
    P.baseArc.cap_band_lower_tips (by
      intro e
      cases e
      · exact hbase false
      · exact hbase true) j hj i
  have halpha' (j : Fin 3) (hj : j = 0 ∨ j = 2) (i : Fin P.firstSide.chain.count) :=
    P.firstSide.cap_band_lower_tips (by
      intro e
      cases e
      · exact halpha false
      · exact halpha true) j hj i
  have hbeta' (j : Fin 3) (hj : j = 1 ∨ j = 2) (i : Fin P.secondSide.chain.count) :=
    P.secondSide.cap_band_lower_tips (by
      intro e
      cases e
      · exact hbeta false
      · exact hbeta true) j hj i
  have hlower (i : P.BandIndex) : (P.bandData i).band.lowerArc ⊆ (P.bandData i).band.carrier :=
    fun _ hp => (P.bandData i).band.isClosed_carrier.frontier_subset
      ((P.bandData i).band.outer_boundaries_subset_frontier (Or.inl (Or.inl (Or.inl hp))))
  rcases i with i | (i | i)
  · fin_cases j
    · exact hbase' 0 (Or.inl rfl) i
    · exact hbase' 1 (Or.inr rfl) i
    · intro p hp
      exact (disjoint_left.mp P.base_opposite
        (mem_iUnion.mpr ⟨i, hlower (.inl i) hp.2⟩) hp.1).elim
  · fin_cases j
    · exact halpha' 0 (Or.inl rfl) i
    · intro p hp
      exact (disjoint_left.mp P.first_opposite
        (mem_iUnion.mpr ⟨i, hlower (.inr (.inl i)) hp.2⟩) hp.1).elim
    · exact halpha' 2 (Or.inr rfl) i
  · fin_cases j
    · intro p hp
      exact (disjoint_left.mp P.second_opposite
        (mem_iUnion.mpr ⟨i, hlower (.inr (.inr i)) hp.2⟩) hp.1).elim
    · exact hbeta' 1 (Or.inl rfl) i
    · exact hbeta' 2 (Or.inr rfl) i

theorem band_off_lower (i : P.BandIndex) :
    (P.bandData i).band.carrier \ (P.bandData i).band.lowerArc ⊆ U := by
  rcases i with i | (i | i)
  · exact P.baseArc.chain.off_lower i
  · exact P.firstSide.chain.off_lower i
  · exact P.secondSide.chain.off_lower i

theorem cap_face_band_chord (hU : IsOpen U) (F : M64IntrinsicFiniteCornerCapFaces C)
    (e : Fin 3) (j : Bool × Bool)
    (hj : if C.positive e then j = (true, true) else j ≠ (true, true)) (i : P.BandIndex) :
    (F.face e j).carrier ∩ (P.bandData i).band.carrier ⊆
      ((F.face e j).boundary 0).map '' Icc (0 : ℝ) 1 := by
  apply m64Intrinsic_retained_corner_band_inter_subset_chord (C.chart e) (C.radius_pos e)
    (F.face e) (C.positive e) ?_ (F.sector e) (F.second e) (F.first e) (F.chord e)
    (fun j => ⟨F.coordinates e j, F.basis e j, F.smooth e j, F.inverse_smooth e j,
      F.source e j, F.carrier e j, F.boundary e j⟩)
    (P.bandData i).band (disjoint_frontier_iff_isOpen.mpr hU).symm (P.band_off_lower i)
    (C.axes_subset_frontier e) ?_ ?_ j hj
  · simpa only [sectorParameterEquiv_apply, if_true, Prod.fst_zero, Prod.snd_zero, add_zero] using
      C.axes_source e (true, true) (C.radius e) ⟨(C.radius_pos e).le, le_rfl⟩
  · rintro p ⟨(⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩), hp⟩
    · apply P.cap_band_lower_tips e i ⟨?_, hp⟩
      change C.chart e (0, t * C.radius e) ∈ C.carrier e
      rw [C.second_axis]
      exact C.second_axis_mem e _ ⟨mul_nonneg ht.1 (C.radius_pos e).le,
        mul_le_of_le_one_left (C.radius_pos e).le ht.2⟩
    · apply P.cap_band_lower_tips e i ⟨?_, hp⟩
      change C.chart e (t * C.radius e, 0) ∈ C.carrier e
      rw [C.first_axis]
      exact C.first_axis_mem e _ ⟨mul_nonneg ht.1 (C.radius_pos e).le,
        mul_le_of_le_one_left (C.radius_pos e).le ht.2⟩
  · rw [F.occupied_union]
    exact P.cap_band_outer e i

end PoincareConjecture.M64IntrinsicTriangleCollar
