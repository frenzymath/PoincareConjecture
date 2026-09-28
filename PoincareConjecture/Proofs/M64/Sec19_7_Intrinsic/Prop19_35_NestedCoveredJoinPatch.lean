import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedJoinedBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinBandCoverage
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBandInteriorCoverage





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_exists_nested_covered_join_patch
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {A0 A B B1 s t speed : ℝ} (ha0 : A0 < s) (hsA : s < A)
    (hBt : B < t) (hb1 : t < B1) (hspeed : 0 < speed)
    (hai : InjOn alpha (Icc A0 A)) (hbi : InjOn beta (Icc B B1))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = speed • deriv alpha A)
    (hmeet : ∀ x ∈ Icc A0 A, ∀ y ∈ Icc B B1,
      alpha x = beta y → x = A ∧ y = B)
    (hregularA : ∀ x ∈ Ioo A0 A, deriv alpha x ≠ 0)
    (hregularB : ∀ y ∈ Ioo B B1, deriv beta y ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha A ∉ K)
    (havoidA : ∀ x ∈ Ioo A0 A, alpha x ∉ K)
    (havoidB : ∀ y ∈ Ioo B B1, beta y ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc A0 A ∪ beta '' Icc B B1 ∪ K)
    (hfV : frontier V = frontier U)
    (L R : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f g : ℝ → ℝ} {a b c d ua wa ub wb uc wc ud wd ra r rb : ℝ}
    (hab : a < b) (hcd : c < d)
    (C : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a b ua wa ub wb ra r)
    (D : ObliqueBandFaces
      (collarParameterEquiv.trans R).toHomeomorph.toOpenPartialHomeomorph
      g c d uc wc ud wd r rb)
    (hleftC : L (a, f a) = alpha s) (hbaseC : L (b, f b) = alpha A)
    (hbaseD : R (c, g c) = alpha A) (hrightD : R (d, g d) = beta t)
    {w : AnnulusCoordinates} (hdirC : L (ub, wb) = w) (hdirD : R (uc, wc) = w)
    (hlowerC : C.lowerArc = alpha '' Icc s A)
    (hlowerD : D.lowerArc = beta '' Icc B t)
    (hsubC : C.carrier ⊆ closure U) (hsubD : D.carrier ⊆ closure U)
    (hopenC : C.carrier \ C.lowerArc ⊆ U) (hopenD : D.carrier \ D.lowerArc ⊆ U)
    (hinter : C.carrier ∩ D.carrier = segment ℝ (alpha A) (alpha A + r • w)) :
    ∃ cutoff > 0, ∀ sa ∈ Ioo (0 : ℝ) cutoff, ∀ z ∈ Ioo (0 : ℝ) cutoff,
      ∀ sb ∈ Ioo (0 : ℝ) cutoff,
        ∃ (C' : ObliqueBandFaces
          (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
          f a b ua wa ub wb sa z)
          (D' : ObliqueBandFaces
          (collarParameterEquiv.trans R).toHomeomorph.toOpenPartialHomeomorph
          g c d uc wc ud wd z sb),
          (∀ q, C'.coordinates q = C.coordinates q) ∧
          (∀ q, D'.coordinates q = D.coordinates q) ∧
          C'.lowerArc = alpha '' Icc s A ∧ D'.lowerArc = beta '' Icc B t ∧
          C'.band ⊆ C.band ∧ D'.band ⊆ D.band ∧
          C'.carrier ⊆ C.carrier ∧ D'.carrier ⊆ D.carrier ∧
          C'.carrier ⊆ closure U ∧ D'.carrier ⊆ closure U ∧
          C'.carrier \ C'.lowerArc ⊆ U ∧ D'.carrier \ D'.lowerArc ⊆ U ∧
          C'.carrier ∩ C.leftCut = C'.leftCut ∧
          D'.carrier ∩ D.rightCut = D'.rightCut ∧
          C'.rightCut = segment ℝ (alpha A) (alpha A + z • w) ∧
          D'.leftCut = segment ℝ (alpha A) (alpha A + z • w) ∧
          C'.carrier ∩ D'.carrier = segment ℝ (alpha A) (alpha A + z • w) ∧
          (∀ x ∈ Ioc s A, ∃ W : Set AnnulusCoordinates, IsOpen W ∧ alpha x ∈ W ∧
            W ∩ closure U ⊆ C'.carrier ∪ D'.carrier) ∧
          ∀ y ∈ Ico B t, ∃ W : Set AnnulusCoordinates, IsOpen W ∧ beta y ∈ W ∧
            W ∩ closure U ⊆ C'.carrier ∪ D'.carrier := by
  obtain ⟨cutoff, hcutoff, hpatch⟩ := m64Intrinsic_exists_nested_joined_bands
    L R hab hcd C D hbaseC hbaseD hdirC hdirD hinter
  refine ⟨cutoff, hcutoff, ?_⟩
  intro sa hsa z hz sb hsb
  obtain ⟨C', D', hCc, hDc, hCl, hDl, hCb, hDb, hCk, hDk,
      hCcontact, hDcontact, hCcut, hDcut, hCD⟩ := hpatch sa hsa z hz sb hsb
  have hClower : C'.lowerArc = alpha '' Icc s A := hCl.trans hlowerC
  have hDlower : D'.lowerArc = beta '' Icc B t := hDl.trans hlowerD
  have hClowerSub : C'.lowerArc ⊆ alpha '' Icc A0 A :=
    hClower.subset.trans (image_mono (Icc_subset_Icc ha0.le le_rfl))
  have hDlowerSub : D'.lowerArc ⊆ beta '' Icc B B1 :=
    hDlower.subset.trans (image_mono (Icc_subset_Icc le_rfl hb1.le))
  have hCregion : C'.carrier ⊆ closure U := hCk.trans hsubC
  have hDregion : D'.carrier ⊆ closure U := hDk.trans hsubD
  have hCopen : C'.carrier \ C'.lowerArc ⊆ U := by
    rintro q ⟨hq, hn⟩
    exact hopenC ⟨hCk hq, fun h => hn (hCl.symm ▸ h)⟩
  have hDopen : D'.carrier \ D'.lowerArc ⊆ U := by
    rintro q ⟨hq, hn⟩
    exact hopenD ⟨hDk hq, fun h => hn (hDl.symm ▸ h)⟩
  have hjoin := m64Intrinsic_straight_join_bands_cover_region ha hb
    (ha0.trans hsA) (hBt.trans hb1) hspeed hai hbi hend hreg htan
    hK hpK hU hV hUV hfront hfV L R C' D'
    hbaseC hbaseD hdirC hdirD hCD hClowerSub hDlowerSub hCregion hDregion
  refine ⟨C', D', hCc, hDc, hClower, hDlower, hCb, hDb, hCk, hDk,
    hCregion, hDregion, hCopen, hDopen, hCcontact, hDcontact, hCcut, hDcut, hCD, ?_, ?_⟩
  · intro x hx
    by_cases hxA : x = A
    · exact hxA.symm ▸ hjoin
    have hx' : x ∈ Ioo A0 A := ⟨ha0.trans hx.1, lt_of_le_of_ne hx.2 hxA⟩
    have hother : alpha x ∉ beta '' Icc B B1 ∪ K := by
      rintro (⟨y, hy, he⟩ | hk)
      · exact hxA (hmeet x (Ioo_subset_Icc_self hx') y hy he.symm).1
      · exact havoidA x hx' hk
    have hf : frontier U = alpha '' Icc A0 A ∪ (beta '' Icc B B1 ∪ K) := by
      simpa only [union_assoc] using hfront
    have hpoint : alpha x ∈ C'.lowerArc := hClower.symm ▸ ⟨x, Ioc_subset_Icc_self hx, rfl⟩
    have hends (e : Bool) : alpha x ≠ (C'.endpointEdge e).map 0 := by
      cases e
      · rw [m64Intrinsic_band_left_endpoint_zero, hleftC]
        intro he
        exact hx.1.ne' (hai (Ioo_subset_Icc_self hx') ⟨ha0.le, hsA.le⟩ he)
      · rw [m64Intrinsic_band_right_endpoint_zero, hbaseC]
        intro he
        exact hxA (hai (Ioo_subset_Icc_self hx') ⟨(ha0.trans hsA).le, le_rfl⟩ he)
    obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_arc_band_covers_lower_interior ha hai
      hregularA hx' ((isCompact_Icc.image hb.continuous).union hK) hother
      hU hV hUV hf hfV C' hClowerSub hpoint hends hCregion
    exact ⟨W, hW, hpW, hcover.trans subset_union_left⟩
  · intro y hy
    by_cases hyB : y = B
    · obtain ⟨W, hW, hpW, hcover⟩ := hjoin
      exact ⟨W, hW, by simpa only [hyB, ← hend] using hpW, hcover⟩
    have hy' : y ∈ Ioo B B1 := ⟨lt_of_le_of_ne hy.1 (Ne.symm hyB), hy.2.trans hb1⟩
    have hother : beta y ∉ alpha '' Icc A0 A ∪ K := by
      rintro (⟨x, hx, he⟩ | hk)
      · exact hyB (hmeet x hx y (Ioo_subset_Icc_self hy') he).2
      · exact havoidB y hy' hk
    have hf : frontier U = beta '' Icc B B1 ∪ (alpha '' Icc A0 A ∪ K) := by
      rw [hfront]
      ac_rfl
    have hpoint : beta y ∈ D'.lowerArc := hDlower.symm ▸ ⟨y, Ico_subset_Icc_self hy, rfl⟩
    have hends (e : Bool) : beta y ≠ (D'.endpointEdge e).map 0 := by
      cases e
      · rw [m64Intrinsic_band_left_endpoint_zero, hbaseD, hend]
        intro he
        exact hyB (hbi (Ioo_subset_Icc_self hy') ⟨le_rfl, (hBt.trans hb1).le⟩ he)
      · rw [m64Intrinsic_band_right_endpoint_zero, hrightD]
        intro he
        exact hy.2.ne (hbi (Ioo_subset_Icc_self hy') ⟨hBt.le, hb1.le⟩ he)
    obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_arc_band_covers_lower_interior hb hbi
      hregularB hy' ((isCompact_Icc.image ha.continuous).union hK) hother
      hU hV hUV hf hfV D' hDlowerSub hpoint hends hDregion
    exact ⟨W, hW, hpW, hcover.trans subset_union_right⟩

end PoincareConjecture
