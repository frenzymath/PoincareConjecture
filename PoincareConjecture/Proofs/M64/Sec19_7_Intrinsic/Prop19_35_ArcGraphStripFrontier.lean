import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphStripFrontier

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_arc_graph_neighborhood_of_interval
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {A B a b : ℝ}
    (hinj : InjOn gamma (Icc A B)) (_hab : a ≤ b) (ha : A < a) (hb : b < B)
    {K : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Icc a b, gamma t ∉ K)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hI : Icc a b ⊆ G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t))) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma '' Icc a b ⊆ W ∧
      ∀ z ∈ W, z ∈ gamma '' Icc A B ∪ K ↔ (L z).2 = f (L z).1 := by
  let tail := gamma '' (Icc A B \ G.source)
  have htail : IsClosed tail :=
    ((isCompact_Icc.diff G.open_source).image hg).isClosed
  let W := (fun z : AnnulusCoordinates => (L z).1) ⁻¹'
    (G.target ∩ G.symm ⁻¹' Ioo A B) \ (tail ∪ K)
  have hW : IsOpen W :=
    ((G.symm.isOpen_inter_preimage isOpen_Ioo).preimage L.continuous.fst).sdiff
      (htail.union hK.isClosed)
  refine ⟨W, hW, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have htG := hI ht
    have htAB : t ∈ Icc A B := ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
    refine ⟨?_, ?_⟩
    · change (L (gamma t)).1 ∈ G.target ∧ G.symm (L (gamma t)).1 ∈ Ioo A B
      rw [hgraph t htG, G.left_inv htG]
      exact ⟨G.map_source htG, ha.trans_le ht.1, ht.2.trans_lt hb⟩
    · rintro (⟨s, hs, hst⟩ | htk)
      · exact hs.2 ((hinj hs.1 htAB hst) ▸ htG)
      · exact havoid t ht htk
  · intro z hz
    have hzG : (L z).1 ∈ G.target := hz.1.1
    have hzAB : G.symm (L z).1 ∈ Ioo A B := hz.1.2
    constructor
    · rintro (⟨s, hs, hsz⟩ | hzK)
      · have hsG : s ∈ G.source := by
          by_contra hn
          exact hz.2 (Or.inl ⟨s, ⟨hs, hn⟩, hsz⟩)
        rw [← hsz, hgraph s hsG]
      · exact False.elim (hz.2 (Or.inr hzK))
    · intro heq
      refine Or.inl ⟨G.symm (L z).1, Ioo_subset_Icc_self hzAB, ?_⟩
      apply L.injective
      rw [hgraph _ (G.map_target hzG), G.right_inv hzG]
      exact Prod.ext rfl heq.symm

set_option maxHeartbeats 800000 in

theorem m64Intrinsic_exists_arc_graph_strip_frontier_chart
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {A B a b : ℝ}
    (hinj : InjOn gamma (Icc A B)) (hab : a < b) (ha : A < a) (hb : b < B)
    {K : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Icc a b, gamma t ∉ K)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f G.target)
    (hI : Icc a b ⊆ G.source) (hmono : StrictMonoOn G G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    (himage : G '' Icc a b = Icc (G a) (G b))
    (htarget : Icc (G a) (G b) ⊆ G.target)
    {ua wa ub wb : ℝ} (P : TransverseGraphCuts f (G a) (G b) ua wa ub wb) :
    ∃ delta > 0, ∃ H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates,
      Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ H.source ∧
      (∀ q, H q = P.linearCoordinates L.symm G.open_target hf q) ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      ∀ q ∈ H.source, H q ∈ gamma '' Icc A B ∪ K ↔ q.2 = 0 := by
  obtain ⟨W, hW, hcover, hlocal⟩ := m64Intrinsic_arc_graph_neighborhood_of_interval
    hg hinj hab.le ha hb hK havoid L G hI hgraph
  let F := P.linearCoordinates L.symm G.open_target hf
  have hGab : G a < G b := hmono (hI (left_mem_Icc.mpr hab.le))
    (hI (right_mem_Icc.mpr hab.le)) hab
  have haxis := m64Intrinsic_graph_strip_axis_image L G hf hI hGab.le hgraph himage P
  let V := F.source ∩ F ⁻¹' W
  have hV : IsOpen V := F.isOpen_inter_preimage hW
  let H := F.restrOpen V hV
  have haxisH (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t, (0 : ℝ)) ∈ H.source := by
    have hs := P.linearCoordinates_axis_mem_source L.symm G.open_target hf hGab htarget ht
    refine ⟨hs, hs, hcover ?_⟩
    rw [← haxis]
    exact ⟨t, ht, rfl⟩
  obtain ⟨delta, hdelta, hstrip⟩ := exists_strip_source_width H haxisH
  have hFi : ContDiffOn ℝ ∞ F.symm F.target :=
    (P.smooth_coordinates_symm G.open_target hf).comp L.contDiff.contDiffOn
      (fun _ hz => hz.2)
  refine ⟨delta, hdelta, H, hstrip, fun _ => rfl,
    (P.smooth_linearCoordinates L.symm G.open_target hf).mono inter_subset_left,
    hFi.mono inter_subset_left, ?_⟩
  intro q hq
  change F q ∈ gamma '' Icc A B ∪ K ↔ q.2 = 0
  rw [hlocal _ hq.2.2, P.linearCoordinates_apply, P.coordinates_apply,
    L.apply_symm_apply]
  change f _ + q.2 = f _ ↔ q.2 = 0
  exact add_eq_left

end PoincareConjecture
