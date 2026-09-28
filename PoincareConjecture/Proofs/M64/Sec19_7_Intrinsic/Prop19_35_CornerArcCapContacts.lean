import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCollarBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConcreteChainEndpoints
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerBandChords

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem lower_subset_carrier (B : M64IntrinsicLinearBandData) :
    B.band.lowerArc ⊆ B.band.carrier :=
  fun _ hp => B.band.isClosed_carrier.frontier_subset
    (B.band.outer_boundaries_subset_frontier (Or.inl (Or.inl (Or.inl hp))))

private theorem optional_subset (p : Prop) [Decidable p] (S : Set AnnulusCoordinates) :
    (if p then S else ∅) ⊆ S := by
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

namespace M64IntrinsicCornerArcCollar

variable {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
  {U : Set AnnulusCoordinates} {C : M64IntrinsicFiniteCornerCaps alpha beta A B U}
  {corner : Bool → J} {sigma : ℝ → AnnulusCoordinates} {T : ℝ}
  (D : M64IntrinsicCornerArcCollar C corner sigma T)

theorem cap_band_outer (j : J) (hincident : j = corner false ∨ j = corner true)
    (i : Fin D.chain.count) : C.carrier j ∩ (D.chain.band i).carrier ⊆
      (D.chain.band i).leftCut ∪ (D.chain.band i).rightCut := by
  intro p hp
  have hcap : p ∈ C.carrier (corner false) ∪ C.carrier (corner true) := by
    rcases hincident with rfl | rfl
    · exact Or.inl hp.1
    · exact Or.inr hp.1
  rcases (D.cap_contact i).subset ⟨hcap, hp.2⟩ with h | h
  · exact Or.inl (optional_subset _ _ h)
  · exact Or.inr (optional_subset _ _ h)

theorem cap_band_lower_tips
    (htip : ∀ e : Bool,
      sigma (if e then T - C.radius (corner e) else C.radius (corner e)) ∈
        ({C.chart (corner e) (C.radius (corner e), 0),
          C.chart (corner e) (0, C.radius (corner e))} : Set AnnulusCoordinates))
    (j : J) (hincident : j = corner false ∨ j = corner true) (i : Fin D.chain.count) :
    C.carrier j ∩ (D.chain.band i).lowerArc ⊆
      {C.chart j (C.radius j, 0), C.chart j (0, C.radius j)} := by
  intro p hp
  have hown (e : Bool) (h : p ∈ ({C.chart (corner e) (C.radius (corner e), 0),
      C.chart (corner e) (0, C.radius (corner e))} : Set AnnulusCoordinates)) :
      p ∈ ({C.chart j (C.radius j, 0), C.chart j (0, C.radius j)} : Set AnnulusCoordinates) := by
    by_cases he : j = corner e
    · simpa only [he] using h
    · have hmem : p ∈ C.carrier (corner e) := by
        rcases h with h | h
        · have ht := ((C.frontier_contact (corner e)).symm.subset
            (Or.inl ⟨C.radius (corner e), ⟨(C.radius_pos _).le, le_rfl⟩,
              (C.first_axis (corner e) (C.radius (corner e))).symm⟩)).1
          exact h.symm ▸ ht
        · have ht := ((C.frontier_contact (corner e)).symm.subset
            (Or.inr ⟨C.radius (corner e), ⟨(C.radius_pos _).le, le_rfl⟩,
              (C.second_axis (corner e) (C.radius (corner e))).symm⟩)).1
          exact h.symm ▸ ht
      exact (disjoint_left.mp (C.separated he) hp.1 hmem).elim
  have hcap : p ∈ C.carrier (corner false) ∪ C.carrier (corner true) := by
    rcases hincident with rfl | rfl
    · exact Or.inl hp.1
    · exact Or.inr hp.1
  have hpband := lower_subset_carrier (.ofChain D.chain i) hp.2
  rcases (D.cap_contact i).subset ⟨hcap, hpband⟩ with h | h
  · by_cases hcut : D.chain.cut i.castSucc = C.radius (corner (if D.reversed then true else false))
    · rw [if_pos hcut] at h
      have hb := lower_cut_base (.ofChain D.chain i) false h hp.2
      change p = ((D.chain.band i).endpointEdge false).map 0 at hb
      rw [D.chain.endpoint_zero] at hb
      change p = sigma (if D.reversed then T - D.chain.cut i.castSucc
        else D.chain.cut i.castSucc) at hb
      rw [hcut] at hb
      apply hown (if D.reversed then true else false)
      have heq : p = sigma (if (if D.reversed then true else false) then
          T - C.radius (corner (if D.reversed then true else false))
          else C.radius (corner (if D.reversed then true else false))) := by
        cases hrev : D.reversed <;>
          simpa only [hrev, Bool.false_eq_true, if_false, if_true] using hb
      rw [heq]
      exact htip _
    · rw [if_neg hcut] at h
      exact h.elim
  · by_cases hcut : D.chain.cut i.succ = T - C.radius (corner (if D.reversed then false else true))
    · rw [if_pos hcut] at h
      have hb := lower_cut_base (.ofChain D.chain i) true h hp.2
      change p = ((D.chain.band i).endpointEdge true).map 0 at hb
      rw [D.chain.endpoint_zero] at hb
      change p = sigma (if D.reversed then T - D.chain.cut i.succ
        else D.chain.cut i.succ) at hb
      rw [hcut] at hb
      apply hown (if D.reversed then false else true)
      have heq : p = sigma (if (if D.reversed then false else true) then
          T - C.radius (corner (if D.reversed then false else true))
          else C.radius (corner (if D.reversed then false else true))) := by
        cases hrev : D.reversed <;>
          simpa only [hrev, Bool.false_eq_true, if_false, if_true, sub_sub_cancel] using hb
      rw [heq]
      exact htip _
    · rw [if_neg hcut] at h
      exact h.elim

end M64IntrinsicCornerArcCollar

end PoincareConjecture
