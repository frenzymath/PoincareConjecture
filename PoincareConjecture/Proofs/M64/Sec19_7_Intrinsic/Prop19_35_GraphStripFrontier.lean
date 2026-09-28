import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopInwardCollar














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem interval_buffer {X : Set ℝ} (hX : IsOpen X)
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ X) :
    ∃ l u : ℝ, l < a ∧ b < u ∧ Ioo l u ⊆ X := by
  obtain ⟨l, r, hlr, hleft⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hX.mem_nhds (hI (left_mem_Icc.mpr hab)))
  obtain ⟨s, u, hsu, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hX.mem_nhds (hI (right_mem_Icc.mpr hab)))
  refine ⟨l, u, hlr.1, hsu.2, ?_⟩
  intro t ht
  by_cases hta : t < a
  · exact hleft ⟨ht.1, hta.trans hlr.2⟩
  by_cases hbt : b < t
  · exact hright ⟨hsu.1.trans hbt, ht.2⟩
  exact hI ⟨le_of_not_gt hta, le_of_not_gt hbt⟩




theorem m64Intrinsic_loop_graph_neighborhood_of_interval
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a ≤ b) (ha : 0 < a) (hb : b < T)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hI : Icc a b ⊆ G.source) (hmono : StrictMonoOn G G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t))) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma '' Icc a b ⊆ W ∧
      ∀ z ∈ W, z ∈ gamma '' Icc 0 T ↔ (L z).2 = f (L z).1 := by
  obtain ⟨l, u, hla, hbu, hsub⟩ := interval_buffer G.open_source hab hI
  let R := G.restrOpen (Ioo l u) isOpen_Ioo
  have hRsource : R.source = Ioo l u := inter_eq_right.mpr hsub
  have hRmono : StrictMonoOn R R.source := fun _ hx _ hy hxy => hmono hx.1 hy.1 hxy
  obtain ⟨W, hW, hcover, hlocal⟩ := m64Intrinsic_loop_graph_neighborhood hg hend hinj
    L R f hab ha hb hla hbu hRsource hRmono (fun t ht => hgraph t ht.1)
  exact ⟨W, hW, hcover, fun z hz => (hlocal z hz).2⟩

set_option maxHeartbeats 800000 in




theorem m64Intrinsic_exists_graph_strip_frontier_chart
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a < b) (ha : 0 < a) (hb : b < T)
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
      ∀ q ∈ H.source, H q ∈ gamma '' Icc 0 T ↔ q.2 = 0 := by
  obtain ⟨W, hW, hcover, hlocal⟩ := m64Intrinsic_loop_graph_neighborhood_of_interval
    hg hend hinj hab.le ha hb L G hI hmono hgraph
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
  change F q ∈ gamma '' Icc 0 T ↔ q.2 = 0
  rw [hlocal _ hq.2.2, P.linearCoordinates_apply, P.coordinates_apply,
    L.apply_symm_apply]
  change f _ + q.2 = f _ ↔ q.2 = 0
  exact add_eq_left

end PoincareConjecture
