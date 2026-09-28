import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandChainFrontier
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCutContacts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RelativeBoundaryCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem exists_adjacent_cell {n : ℕ} (c : Fin (n + 1) → ℝ)
    {p : ℝ} (hp0 : c 0 < p) (hplast : p < c (Fin.last n)) :
    ∃ i : Fin n, p ∈ Icc (c i.castSucc) (c i.succ) := by
  classical
  have hex : ∃ k : Fin (n + 1), p < c k := ⟨Fin.last n, hplast⟩
  let j := Fin.find (fun k => p < c k) hex
  have hj : p < c j := Fin.find_spec hex
  have hjpos : 0 < j.val := by
    by_contra hn
    have hzero : j = 0 := Fin.ext (show j.val = 0 by omega)
    rw [hzero] at hj
    linarith
  let i : Fin n := ⟨j.val - 1, by have h := j.isLt; omega⟩
  have hij : i.succ = j := Fin.ext (by dsimp [i]; omega)
  refine ⟨i, ?_, hij ▸ hj.le⟩
  exact le_of_not_gt (Fin.find_min hex (show i.castSucc < j by
    rw [← hij]
    exact Fin.castSucc_lt_succ))

theorem m64Intrinsic_trimmed_band_chain_covers_region
    {gamma d : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {T a b : ℝ} (ha : 0 < a) (hb : b < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    {n : ℕ} (c : Fin (n + 1) → ℝ) (hc : StrictMono c)
    (hfirst : c 0 = a) (hlast : c (Fin.last n) = b)
    (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ)
    (lengths : Fin (n + 1) → ℝ)
    (B : ∀ i : Fin n,
      ObliqueBandFaces
        (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
        (f i) (G i (c i.castSucc)) (G i (c i.succ))
        (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
        (L i (d (c i.succ))).1 (L i (d (c i.succ))).2
        (lengths i.castSucc) (lengths i.succ))
    (hboundary : ∀ i, (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) ∧
      (B i).leftCut = segment ℝ (gamma (c i.castSucc))
        (gamma (c i.castSucc) + lengths i.castSucc • d (c i.castSucc)) ∧
      (B i).rightCut = segment ℝ (gamma (c i.succ))
        (gamma (c i.succ) + lengths i.succ • d (c i.succ)))
    (hregion : ∀ i, (B i).carrier ⊆ closure U ∧ (B i).carrier \ (B i).lowerArc ⊆ U)
    (hadj : ∀ i j : Fin n, i.succ = j.castSucc →
      (B i).carrier ∩ (B j).carrier = segment ℝ (gamma (c i.succ))
        (gamma (c i.succ) + lengths i.succ • d (c i.succ))) :
    ∀ p ∈ Ioo a b, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ gamma p ∈ W ∧ W ∩ closure U ⊆ ⋃ i, (B i).carrier := by
  classical
  intro p hp
  let K := ⋃ i, (B i).carrier
  let E := (⋃ i, (B i).polygonalTop) ∪
    (⋃ i, ⋃ (_ : c i.castSucc = a), (B i).leftCut) ∪
      (⋃ i, ⋃ (_ : c i.succ = b), (B i).rightCut)
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite (fun i => (B i).isClosed_carrier)
  have hKregular : closure (interior K) = K :=
    Poincare.Topology.closure_interior_iUnion_of_regular_closed
      (fun i => (B i).carrier) (fun i => (B i).isClosed_carrier)
      (fun i => (B i).closure_interior_carrier)
  have hKsub : K ⊆ closure U := iUnion_subset (fun i => (hregion i).1)
  have hpT : p ∈ Ioo (0 : ℝ) T := ⟨ha.trans hp.1, hp.2.trans hb⟩
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a b := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hcutT (k : Fin (n + 1)) : c k ∈ Ico (0 : ℝ) T :=
    ⟨ha.le.trans (hcut k).1, (hcut k).2.trans_lt hb⟩
  have hpK : gamma p ∈ K := by
    obtain ⟨i, hi⟩ := exists_adjacent_cell c (hfirst ▸ hp.1) (hlast ▸ hp.2)
    apply mem_iUnion.mpr
    refine ⟨i, (B i).isClosed_carrier.frontier_subset ?_⟩
    apply (B i).outer_boundaries_subset_frontier
    apply Or.inl (Or.inl (Or.inl ?_))
    rw [(hboundary i).1]
    exact ⟨p, hi, rfl⟩
  have hloopdisj : Disjoint U (gamma '' Icc 0 T) := by
    have h : Disjoint (interior U) (frontier U) := disjoint_interior_frontier
    simpa only [hU.interior_eq, hfU] using h
  have hpLoop : gamma p ∈ gamma '' Icc 0 T := ⟨p, Ioo_subset_Icc_self hpT, rfl⟩
  have hbaseLeft (i : Fin n) : ((B i).endpointEdge false).map 0 = gamma (c i.castSucc) := by
    rw [m64Intrinsic_band_left_endpoint_zero]
    have h := m64Intrinsic_band_left_cut (L i).symm (B i)
    simp only [Prod.eta, (L i).symm_apply_apply] at h
    exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hboundary i).2.1)
  have hbaseRight (i : Fin n) : ((B i).endpointEdge true).map 0 = gamma (c i.succ) := by
    rw [m64Intrinsic_band_right_endpoint_zero]
    have h := m64Intrinsic_band_right_cut (L i).symm (B i)
    simp only [Prod.eta, (L i).symm_apply_apply] at h
    exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hboundary i).2.2)
  have hcompactCut (i : Fin n) (right : Bool) :
      IsCompact (if right then (B i).rightCut else (B i).leftCut) := by
    have h : IsCompact (((B i).endpointEdge right).map '' Icc (0 : ℝ) 1) :=
      isCompact_Icc.image_of_continuousOn ((B i).endpointEdge right).smooth.continuousOn
    exact (B i).endpointEdge_image right ▸ h
  have hTop : IsCompact (⋃ i, (B i).polygonalTop) :=
    isCompact_iUnion (fun i => (B i).isCompact_polygonalTop)
  have hLeft : IsCompact (⋃ i, ⋃ (_ : c i.castSucc = a), (B i).leftCut) := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro _
    have h := hcompactCut i false
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact h
  have hRight : IsCompact (⋃ i, ⋃ (_ : c i.succ = b), (B i).rightCut) := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro _
    have h := hcompactCut i true
    simp only [↓reduceIte] at h
    exact h
  have hEcompact : IsCompact E := (hTop.union hLeft).union hRight
  have hpE : gamma p ∉ E := by
    rintro ((htop | hleft) | hright)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp htop
      exact disjoint_left.mp hloopdisj
        (m64Intrinsic_band_top_subset_region (B i) (hregion i).2 hi) hpLoop
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hleft
      obtain ⟨hia, hi⟩ := mem_iUnion.mp hi
      have h := m64Intrinsic_band_cut_contact_subset_base (B i) false (hregion i).2
        hloopdisj ⟨hi, hpLoop⟩
      rw [mem_singleton_iff, hbaseLeft] at h
      have hpi := hinj (Ioo_subset_Ico_self hpT) (hcutT i.castSucc) h
      exact hp.1.ne' (hpi.trans hia)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hright
      obtain ⟨hib, hi⟩ := mem_iUnion.mp hi
      have h := m64Intrinsic_band_cut_contact_subset_base (B i) true (hregion i).2
        hloopdisj ⟨hi, hpLoop⟩
      rw [mem_singleton_iff, hbaseRight] at h
      have hpi := hinj (Ioo_subset_Ico_self hpT) (hcutT i.succ) h
      exact hp.2.ne (hpi.trans hib)
  apply m64Intrinsic_exists_relative_cover_of_local_frontier hg hend hinj hregular hpT
    hU hV hdisj hfU hfV hKclosed hKregular hKsub hpK
    (hEcompact.isClosed.isOpen_compl.mem_nhds hpE)
  intro z hz
  have hfront := (m64Intrinsic_band_chain_frontier c hc hfirst hlast L G f lengths B
    hboundary hadj).2 hz.2
  rcases hfront with ((hlower | htop) | hleft) | hright
  · obtain ⟨t, ht, rfl⟩ := hlower
    exact ⟨t, ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩, rfl⟩
  · exact False.elim (hz.1 (Or.inl (Or.inl htop)))
  · exact False.elim (hz.1 (Or.inl (Or.inr hleft)))
  · exact False.elim (hz.1 (Or.inr hright))

end PoincareConjecture
