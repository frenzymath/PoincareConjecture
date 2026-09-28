import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.CornerArcOrder

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

def edgeIntervals (a b c d : ℝ) : Set (ℝ × ℝ) :=
  ({0} ×ˢ Icc b d) ∪ (Icc a c ×ˢ {0})

private theorem rimArc_mono {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) :
    rimArc a b ⊆ rimArc c d := by
  unfold rimArc RectangleCornerArcs.cornerArc
  rw [uIcc_of_le ha, uIcc_of_le hb, uIcc_of_le (ha.trans hac),
    uIcc_of_le (hb.trans hbd)]
  exact union_subset_union (prod_mono Subset.rfl (Icc_subset_Icc le_rfl hbd))
    (prod_mono (Icc_subset_Icc le_rfl hac) Subset.rfl)

private theorem rimArc_difference {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hac : a < c) (hbd : b < d) :
    rimArc c d \ (rimArc a b \ {(0, b), (a, 0)}) = edgeIntervals a b c d := by
  ext p
  simp only [rimArc, RectangleCornerArcs.cornerArc, edgeIntervals,
    uIcc_of_le ha.le, uIcc_of_le hb.le, uIcc_of_le (ha.trans hac).le,
    uIcc_of_le (hb.trans hbd).le, mem_sdiff, mem_union, mem_prod,
    mem_singleton_iff, mem_Icc, mem_insert_iff]
  constructor
  · rintro ⟨h | h, hn⟩
    · left
      refine ⟨h.1, ?_, h.2.2⟩
      by_contra hlt
      apply hn
      refine ⟨Or.inl ⟨h.1, h.2.1, (lt_of_not_ge hlt).le⟩, ?_⟩
      simp only [Prod.ext_iff]
      rintro (he | he)
      · exact (lt_of_not_ge hlt).ne he.2
      · exact ha.ne (h.1.symm.trans he.1)
    · right
      refine ⟨⟨?_, h.1.2⟩, h.2⟩
      by_contra hlt
      apply hn
      refine ⟨Or.inr ⟨⟨h.1.1, (lt_of_not_ge hlt).le⟩, h.2⟩, ?_⟩
      simp only [Prod.ext_iff]
      rintro (he | he)
      · exact hb.ne (h.2.symm.trans he.2)
      · exact (lt_of_not_ge hlt).ne he.1
  · rintro (h | h)
    · refine ⟨Or.inl ⟨h.1, hb.le.trans h.2.1, h.2.2⟩, ?_⟩
      rintro ⟨hi | hi, hn⟩
      · apply hn
        exact Or.inl (Prod.ext h.1 (le_antisymm hi.2.2 h.2.1))
      · exact (hb.trans_le h.2.1).ne' hi.2
    · refine ⟨Or.inr ⟨⟨ha.le.trans h.1.1, h.1.2⟩, h.2⟩, ?_⟩
      rintro ⟨hi | hi, hn⟩
      · exact (ha.trans_le h.1.1).ne' hi.1
      · apply hn
        exact Or.inr (Prod.ext (le_antisymm hi.1.2 h.1.1) h.2)

theorem exists_corner_arc_strip
    {a b c d : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    {W Z : Set (ℝ × ℝ)} (hW : IsFinitePLBallPair ℝ W {(0, b), (a, 0)})
    (hZ : IsFinitePLBallPair ℝ Z {(0, d), (c, 0)})
    (hproperW : W \ {(0, b), (a, 0)} ⊆ base \ frontier base)
    (hproperZ : Z \ {(0, d), (c, 0)} ⊆ base \ frontier base)
    (hdis : Disjoint W Z) (hac : a < c) :
    ∃ A M D V : Set (ℝ × ℝ),
      IsFinitePLBallPair (ℝ × ℝ) A (rimArc a b ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) M (W ∪ (Z ∪ edgeIntervals a b c d)) ∧
      IsFinitePLBallPair (ℝ × ℝ) D (Z ∪ V) ∧
      (A ∪ M) ∪ D = base ∧ A ∩ M = W ∧ M ∩ D = Z ∧ Disjoint A D ∧
      A ∩ frontier base = rimArc a b ∧
      M ∩ frontier base = edgeIntervals a b c d ∧ D ∩ frontier base = V := by
  have hbd := (endpoint_order_of_disjoint_arcs ha hb hc hd hW hZ
    hproperW hproperZ hdis).2.2.mp hac
  obtain ⟨C, D, V, hV, hUV, hUiV, hC, hD, hCD, hCiD, hCB, hDB, _, _⟩ :=
    exists_corner_arc_cut hc hd hZ hproperZ
  have hUsub := rimArc_mono ha.1.le hb.1.le hac.le hbd.le
  have hWC : W ⊆ C := by
    have hWbase : W ⊆ base := by
      intro x hx
      by_cases he : x ∈ ({(0, b), (a, 0)} : Set (ℝ × ℝ))
      · exact isFinitePLBallPair_base.1
          (rimArc_subset_frontier ha hb ((rimArc_ballPair ha.1 hb.1).1 he))
      · exact (hproperW ⟨hx, he⟩).1
    rcases Dehn.isPreconnected_subset_one_cut_piece hW.isConnected.isPreconnected
        hC.isCompact.isClosed hD.isCompact.isClosed (hWbase.trans hCD.symm.subset)
        hCiD hdis with hWC | hWD
    · exact hWC
    · have hxW : ((0 : ℝ), b) ∈ W := hW.1 (by simp)
      have hxC : ((0 : ℝ), b) ∈ C :=
        hC.1 (Or.inl (hUsub ((rimArc_ballPair ha.1 hb.1).1 (by simp))))
      exact False.elim (disjoint_left.mp hdis hxW (hCiD.subset ⟨hxC, hWD hxW⟩))
  have hab : ((0 : ℝ), b) ≠ (a, 0) := by
    intro he
    exact ha.1.ne (congrArg Prod.fst he)
  obtain ⟨T, hT, hUT, hUiT⟩ := hC.exists_boundary_arc_complement
    (rimArc_ballPair ha.1 hb.1) (hUsub.trans subset_union_left) hab
  have hZU : Disjoint Z (rimArc a b) := by
    apply disjoint_left.mpr
    intro x hxZ hxU
    have hxB := rimArc_subset_frontier ha hb hxU
    have hxend : x ∈ ({(0, d), (c, 0)} : Set (ℝ × ℝ)) := by
      by_contra hn
      exact (hproperZ ⟨hxZ, hn⟩).2 hxB
    rcases hxend with rfl | he
    · rcases hxU with hi | hi
      · exact (not_le_of_gt hbd) ((uIcc_of_le hb.1.le ▸ hi.2).2)
      · exact hd.1.ne' hi.2
    · have he' : x = (c, 0) := mem_singleton_iff.mp he
      subst x
      rcases hxU with hi | hi
      · exact hc.1.ne' hi.1
      · exact (not_le_of_gt hac) ((uIcc_of_le ha.1.le ▸ hi.1).2)
  have hTeq : T = Z ∪ edgeIntervals a b c d := by
    have hdiff : T = (rimArc c d ∪ Z) \ (rimArc a b \ {(0, b), (a, 0)}) := by
      ext x
      constructor
      · intro hx
        refine ⟨hUT.subset (Or.inr hx), ?_⟩
        exact fun hn => hn.2 (hUiT.subset ⟨hn.1, hx⟩)
      · rintro ⟨hx, hn⟩
        rcases hUT.symm.subset hx with hxU | hxT
        · have he : x ∈ ({(0, b), (a, 0)} : Set (ℝ × ℝ)) :=
            Classical.byContradiction (fun he => hn ⟨hxU, he⟩)
          exact hT.1 he
        · exact hxT
    rw [hdiff, union_sdiff_distrib, rimArc_difference ha.1 hb.1 hac hbd]
    have hZd : Z \ (rimArc a b \ {(0, b), (a, 0)}) = Z := by
      apply Subset.antisymm sdiff_subset
      exact fun x hx => ⟨hx, fun hn => disjoint_left.mp hZU hx hn.1⟩
    rw [hZd, union_comm]
  have hproperC : W \ {(0, b), (a, 0)} ⊆ C \ (rimArc c d ∪ Z) := by
    intro x hx
    refine ⟨hWC hx.1, ?_⟩
    rintro (hxU | hxZ)
    · exact (hproperW hx).2 (rimArc_subset_frontier hc hd hxU)
    · exact disjoint_left.mp hdis hx.1 hxZ
  obtain ⟨A, M, hA, hM, hAM, hAiM, hAq, hMq⟩ :=
    hC.exists_proper_arc_cut (rimArc_ballPair ha.1 hb.1) hT hW hab
      hUiT.subset hUT hproperC
  have hAC : A ⊆ C := subset_union_left.trans hAM.subset
  have hMC : M ⊆ C := subset_union_right.trans hAM.subset
  have hZM : Z ⊆ M := by
    intro x hx
    exact hM.1 (Or.inr (hTeq.symm.subset (Or.inl hx)))
  have hAD : Disjoint A D := by
    apply disjoint_left.mpr
    intro x hxA hxD
    have hxZ := hCiD.subset ⟨hAC hxA, hxD⟩
    exact disjoint_left.mp hZU hxZ (hAq.subset ⟨hxA, Or.inr hxZ⟩)
  have hMD : M ∩ D = Z := by
    apply Subset.antisymm
    · exact fun x hx => hCiD.subset ⟨hMC hx.1, hx.2⟩
    · exact fun x hx => ⟨hZM hx, (hCiD.symm.subset hx).2⟩
  have hAB : A ∩ frontier base = rimArc a b := by
    apply Subset.antisymm
    · intro x hx
      exact hAq.subset ⟨hx.1, Or.inl (hCB.subset ⟨hAC hx.1, hx.2⟩)⟩
    · exact fun x hx => ⟨hA.1 (Or.inl hx), rimArc_subset_frontier ha hb hx⟩
  have hMB : M ∩ frontier base = edgeIntervals a b c d := by
    have htemp : M ∩ frontier base = T ∩ rimArc c d := by
      ext x
      constructor
      · intro hx
        have hxU := hCB.subset ⟨hMC hx.1, hx.2⟩
        exact ⟨hMq.subset ⟨hx.1, Or.inl hxU⟩, hxU⟩
      · intro hx
        exact ⟨hM.1 (Or.inr hx.1), rimArc_subset_frontier hc hd hx.2⟩
    rw [htemp]
    have hdiff : T ∩ rimArc c d = rimArc c d \ (rimArc a b \ {(0, b), (a, 0)}) := by
      ext x
      constructor
      · rintro ⟨hxT, hxU⟩
        exact ⟨hxU, fun hn => hn.2 (hUiT.subset ⟨hn.1, hxT⟩)⟩
      · rintro ⟨hxU, hn⟩
        refine ⟨?_, hxU⟩
        rcases hUT.symm.subset (Or.inl hxU) with hi | ht
        · exact hT.1 (Classical.byContradiction (fun he => hn ⟨hi, he⟩))
        · exact ht
    rw [hdiff, rimArc_difference ha.1 hb.1 hac hbd]
  exact ⟨A, M, D, V, hA, hTeq ▸ hM, hD, by rw [hAM, hCD], hAiM, hMD,
    hAD, hAB, hMB, hDB⟩

end PoincareConjecture.M76.TriangleCorner
