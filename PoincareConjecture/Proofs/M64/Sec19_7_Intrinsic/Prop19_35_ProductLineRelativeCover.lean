import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanCorner
import PoincareConjecture.Proofs.Horizon.Topology.Connected.TwoSidedUnion

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_exists_product_line_relative_cover
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hd : Disjoint U V) (hfV : frontier V = frontier U)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {x : ℝ}
    (hx : (x, 0) ∈ H.source) (hpfront : H (x, 0) ∈ frontier U)
    (hline : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ frontier U ↔ z.2 = 0)
    {K : Set AnnulusCoordinates} (hK : IsClosed K)
    (hKregular : closure (interior K) = K) (hKsub : K ⊆ closure U)
    (hpK : H (x, 0) ∈ K) {N : Set AnnulusCoordinates}
    (hN : N ∈ 𝓝 (H (x, 0))) (hfrontK : N ∩ frontier K ⊆ frontier U) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ H (x, 0) ∈ W ∧ W ∩ closure U ⊆ K := by
  have hn := (H.continuousAt hx).preimage_mem_nhds hN
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (H.open_source.mem_nhds hx) (inter_mem hn hline))
  let Q := ball (x, (0 : ℝ)) r
  let P := Q ∩ ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ))
  let M := Q ∩ ((univ : Set ℝ) ×ˢ Iio (0 : ℝ))
  let O := H '' Q
  have hsource : Q ⊆ H.source := fun _ hz => (hball hz).1
  have hO : IsOpen O := H.isOpen_image_of_subset_source isOpen_ball hsource
  have hpO : H (x, 0) ∈ O := mem_image_of_mem H (mem_ball_self hr)
  have hPN : IsPreconnected (H '' P) :=
    (((convex_ball _ _).inter (convex_univ.prod (convex_Ioi (0 : ℝ)))).isPreconnected).image
      H (H.continuousOn.mono (inter_subset_left.trans hsource))
  have hMN : IsPreconnected (H '' M) :=
    (((convex_ball _ _).inter (convex_univ.prod (convex_Iio (0 : ℝ)))).isPreconnected).image
      H (H.continuousOn.mono (inter_subset_left.trans hsource))
  have hPne : (H '' P).Nonempty := by
    refine ⟨H (x, r / 2), mem_image_of_mem H ⟨?_, mem_univ _, half_pos hr⟩⟩
    simpa only [Q, mem_ball, dist_prod_same_left, Real.dist_eq, sub_zero,
      abs_of_pos (half_pos hr)] using half_lt_self hr
  have hMne : (H '' M).Nonempty := by
    refine ⟨H (x, -(r / 2)), mem_image_of_mem H ⟨?_, mem_univ _, neg_neg_of_pos (half_pos hr)⟩⟩
    simpa only [Q, mem_ball, dist_prod_same_left, Real.dist_eq, sub_zero, abs_neg,
      abs_of_pos (half_pos hr)] using half_lt_self hr
  have hpartition : O \ frontier U = (H '' P) ∪ (H '' M) := by
    ext z
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hnot⟩
      have hqne : q.2 ≠ 0 := fun heq => hnot ((hball hq).2.2.mpr heq)
      rcases lt_or_gt_of_ne hqne with hneg | hpos
      · exact Or.inr (mem_image_of_mem H ⟨hq, mem_univ _, hneg⟩)
      · exact Or.inl (mem_image_of_mem H ⟨hq, mem_univ _, hpos⟩)
    · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact ⟨mem_image_of_mem H hq.1, fun hf => hq.2.2.ne' ((hball hq.1).2.2.mp hf)⟩
      · exact ⟨mem_image_of_mem H hq.1, fun hf => hq.2.2.ne ((hball hq.1).2.2.mp hf)⟩
  have hUregular := m64Intrinsic_jordan_interior_closure hU hV hd hfV.symm
  have hVregular := m64Intrinsic_jordan_interior_closure hV hU hd.symm hfV
  have hthin : interior (frontier U) = ∅ := by
    rw [← hUregular.2]
    exact interior_frontier isClosed_closure
  have hdense : Dense (frontier U)ᶜ := interior_eq_empty_iff_dense_compl.mp hthin
  have hOdense : O ⊆ closure ((H '' P) ∪ (H '' M)) := by
    rw [← hpartition]
    intro z hz
    apply _root_.mem_closure_iff.mpr
    intro W hW hzW
    obtain ⟨y, ⟨hyW, hyO⟩, hyf⟩ :=
      hdense.inter_open_nonempty (W ∩ O) (hW.inter hO) ⟨z, hzW, hz⟩
    exact ⟨y, hyW, hyO, hyf⟩
  have hdisjoint : Disjoint (interior K) (interior (closure V)) := by
    rw [hVregular.1]
    apply hd.mono_left
    rw [← hUregular.1]
    exact interior_mono hKsub
  have hpV : H (x, 0) ∈ closure V := frontier_subset_closure (hfV.symm ▸ hpfront)
  have hcover : O ⊆ K ∪ closure V := by
    apply Poincare.Topology.subset_union_of_two_sided_neighborhood hK isClosed_closure
      hKregular (by rw [hVregular.1]) hdisjoint hpK hpV (hO.mem_nhds hpO)
      hpartition hPN hMN hPne hMne hOdense
    · rintro z ⟨⟨q, hq, rfl⟩, hf⟩
      exact hfrontK ⟨(hball hq).2.1, hf⟩
    · intro z hz
      simpa only [hVregular.2, hfV] using hz.2
  refine ⟨O, hO, hpO, ?_⟩
  intro z hz
  apply hK.closure_subset
  apply _root_.mem_closure_iff.mpr
  intro W hW hzW
  obtain ⟨y, ⟨hyW, hyO⟩, hyU⟩ := _root_.mem_closure_iff.mp hz.2
    (W ∩ O) (hW.inter hO) ⟨hzW, hz.1⟩
  refine ⟨y, hyW, ?_⟩
  rcases hcover hyO with hyK | hyV
  · exact hyK
  · exact False.elim (disjoint_left.mp (hd.closure_right hU) hyU hyV)

end PoincareConjecture
