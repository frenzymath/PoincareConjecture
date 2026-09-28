import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedCollarData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcPatchData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedPatchNesting
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcPairedChains
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChainPatchCoverage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_three_arc_joined_collar
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : Continuous sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e)))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hregular : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), deriv (gamma e) t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (hray : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma e t + z • quarterTurn (deriv (gamma e) t) ∈ U)
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) :
    ∃ b : Bool → ℝ, Nonempty (M64IntrinsicJoinedArcCollar C b) := by
  classical
  obtain ⟨b, hb, hgap, P, _, hPavoid⟩ := m64Intrinsic_exists_three_arc_patch_data
    gamma sigma T hg hs hT hS hspeed hinj hjoin hreg htan hab has hbs
    (hregular false) hU hV hUV hfront hfV (hray false) C
  have hrest (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (T e)) :
      gamma e t ∉ gamma (!e) '' Icc 0 (T (!e)) ∪ sigma '' Icc 0 S := by
    cases e
    · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
      · exact ht.2.ne (hab t (Ioo_subset_Icc_self ht) y hy he.symm).1
      · exact ht.1.ne' (has t (Ioo_subset_Icc_self ht) y hy he.symm).1
    · rintro (⟨x, hx, he⟩ | ⟨y, hy, he⟩)
      · exact ht.1.ne' (hab x hx t (Ioo_subset_Icc_self ht) he).2
      · exact ht.2.ne (hbs t (Ioo_subset_Icc_self ht) y hy he.symm).1
  have hpK : gamma false (T false) ∉ sigma '' Icc 0 S := by
    rintro ⟨y, hy, he⟩
    exact (hT false).ne' (has (T false) ⟨(hT false).le, le_rfl⟩ y hy he.symm).1
  obtain ⟨delta, hdelta, hnest⟩ := m64Intrinsic_exists_nested_patch_data gamma T b hg hb
    hspeed hinj hjoin hreg htan hab hregular (isCompact_Icc.image hs) hpK
    (fun e t ht h => hrest e t ht (Or.inr h)) hU hV hUV hfront hfV P
  have htip (e : Bool) : (C.radius e, (0 : ℝ)) ∈ (C.chart e).source := by
    simpa only [sectorParameterEquiv_apply, if_true, Prod.fst_zero, Prod.snd_zero,
      zero_add, one_mul, add_zero] using
      (C.axes_source e (true, true) (C.radius e) ⟨(C.radius_pos e).le, le_rfl⟩).1
  obtain ⟨E, hEdata, hseparated, _, hthird⟩ := m64Intrinsic_exists_three_arc_paired_chains
    gamma sigma T C.radius b hg hs hT hS hdelta C.radius_pos C.radius_bound hb hgap
    hinj hregular hjoin hab has hbs hU hV hUV hfront hfV hray
    C.chart C.cap C.positive
    (fun e i => ⟨C.cap_source e i, C.cap_smooth e i, C.cap_inverse_smooth e i,
      C.cap_first e i, C.cap_second e i, C.cap_chord e i, C.cap_sector e i⟩)
    C.first_axis htip P.frame P.graph P.left P.right
    (fun e => ((P.frame e).symm P.direction).1)
    (fun e => ((P.frame e).symm P.direction).2)
    (fun e => ((P.frame e).symm P.direction).1)
    (fun e => ((P.frame e).symm P.direction).2)
    (fun e => if e then P.middle_length else P.left_length)
    (fun e => if e then P.right_length else P.middle_length)
    P.increasing P.band P.outer_base P.tangent
    (by
      intro e
      simpa only [Prod.eta, ContinuousLinearEquiv.apply_symm_apply, ite_self] using
        P.transverse e)
    P.lower_arc P.off_lower C.occupied hPavoid
    (fun e => (C.frontier_contact e).subset)
    (fun e => ⟨C.neighborhood e, C.neighborhood_open e, C.base_mem e, C.covers_corner e⟩)
  choose hell hsmall hcapdir hdir hcpath _ hother hcontact hcover using hEdata
  have hsmall' (e : Bool) :
      (E e).length * (if e then P.right_length else P.left_length) < delta := by
    cases e <;> exact hsmall _
  have hdir' (e : Bool) : (E e).direction (b e) =
      (if e then P.right_length else P.left_length) • P.direction := by
    cases e
    · simpa only [Prod.eta, ContinuousLinearEquiv.apply_symm_apply,
        Bool.false_eq_true, if_false, if_true] using hdir false
    · simpa only [Prod.eta, ContinuousLinearEquiv.apply_symm_apply,
        Bool.false_eq_true, if_false, if_true] using hdir true
  have hleft : (E false).length * P.left_length ∈ Ioo (0 : ℝ) delta :=
    ⟨mul_pos (E false).length_pos (P.outer_length_pos false), hsmall' false⟩
  have hright : (E true).length * P.right_length ∈ Ioo (0 : ℝ) delta :=
    ⟨mul_pos (E true).length_pos (P.outer_length_pos true), hsmall' true⟩
  obtain ⟨Q, hQdir, hQl, _, hQr, _, hQsub, hQouter, hQcover⟩ :=
    hnest _ hleft (delta / 2) ⟨half_pos hdelta, half_lt_self hdelta⟩ _ hright
  have hCunion (e : Bool) : C.carrier e ⊆ C.carrier false ∪ C.carrier true := by
    cases e
    · exact subset_union_left
    · exact subset_union_right
  have hCP (e : Bool) : Disjoint (C.carrier e)
      ((P.band e).carrier ∪ (P.band (!e)).carrier) := by
    apply disjoint_left.mpr
    rintro p hpC (hp | hp)
    · exact hPavoid e hp (Or.inl (hCunion e hpC))
    · exact hPavoid (!e) hp (Or.inl (hCunion e hpC))
  have hmatched (e : Bool) := m64Intrinsic_joined_patch_chain_contacts P Q e (E e)
    (hell e) (by cases e <;> rfl)
    (by cases e <;> exact hdir' _) hQdir
    (by
      cases e
      · exact hQl
      · exact hQr)
    (by cases e <;> exact hcpath _) (hCP e) hQsub (hQouter e) (hcontact e)
  have hcut (e : Bool) :
      (if e then (Q.band e).rightCut else (Q.band e).leftCut) =
        segment ℝ (gamma e (b e)) (gamma e (b e) + (E e).length • (E e).direction (b e)) := by
    cases e <;> exact (hmatched _).1
  have hfront' (e : Bool) : frontier U = gamma e '' Icc 0 (T e) ∪
      (gamma (!e) '' Icc 0 (T (!e)) ∪ sigma '' Icc 0 S) := by
    cases e
    · change frontier U = gamma false '' Icc 0 (T false) ∪
        (gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
      exact hfront.trans (union_assoc _ _ _)
    · change frontier U = gamma true '' Icc 0 (T true) ∪
        (gamma false '' Icc 0 (T false) ∪ sigma '' Icc 0 S)
      rw [hfront]
      ac_rfl
  let R := (C.carrier false ∪ C.carrier true) ∪ m64IntrinsicJoinedBandUnion E Q
  have hCinc (e : Bool) : C.carrier e ⊆ R := (hCunion e).trans subset_union_left
  have hEinc (e : Bool) : (⋃ i, ((E e).band i).carrier) ⊆ R :=
    fun _ hp => Or.inr (mem_iUnion.mpr ⟨e, Or.inl hp⟩)
  have hQinc (e : Bool) : (Q.band e).carrier ⊆ R :=
    fun _ hp => Or.inr (mem_iUnion.mpr ⟨e, Or.inr hp⟩)
  have hattachment (e : Bool) : ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      gamma e (b e) ∈ W ∧ W ∩ closure U ⊆ R := by
    have ha : 0 < (if e then b e else C.radius e) := by
      cases e
      · exact C.radius_pos false
      · exact (hb true).1
    have hd : (if e then T e - C.radius e else b e) < T e := by
      cases e
      · exact (hb false).2
      · exact sub_lt_self _ (C.radius_pos true)
    have hlower : (Q.band e).lowerArc ⊆ gamma e '' Icc 0 (T e) := by
      rw [Q.lower_arc]
      cases e
      · exact image_mono (Icc_subset_Icc (hb false).1.le le_rfl)
      · exact image_mono (Icc_subset_Icc le_rfl (hb true).2.le)
    obtain ⟨W, hW, hpW, hcov⟩ := m64Intrinsic_chain_patch_covers_attachment (hg e) ha hd
      (hinj e) (hregular e)
      ((isCompact_Icc.image (hg (!e)).continuous).union (isCompact_Icc.image hs))
      (hrest e) hU hV hUV (hfront' e) hfV (E e) e (Q.band e)
      (by cases e <;> exact Q.outer_endpoint_zero _)
      (hmatched e).1 (fun i => ((hmatched e).2 i).2.1) hlower (Q.occupied e)
    refine ⟨W, hW, ?_, hcov.trans (union_subset (hEinc e) (hQinc e))⟩
    cases e <;> exact hpW
  have hcapSide (e : Bool) (p : ℝ)
      (hp : p ∈ if e then Ioc (b e) (T e) else Ico 0 (b e)) :
      ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma e p ∈ W ∧ W ∩ closure U ⊆ R := by
    obtain ⟨W, hW, hpW, hcov⟩ := hcover e p hp
    exact ⟨W, hW, hpW, hcov.trans (union_subset (hCinc e) (hEinc e))⟩
  have hpatchSide (e : Bool) (p : ℝ)
      (hp : p ∈ if e then Ico 0 (b e) else Ioc (b e) (T e)) :
      ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma e p ∈ W ∧ W ∩ closure U ⊆ R := by
    obtain ⟨W, hW, hpW, hcov⟩ := hQcover e p hp
    exact ⟨W, hW, hpW, hcov.trans (union_subset (hQinc false) (hQinc true))⟩
  refine ⟨b, ⟨{
    attachment := hb
    chain := E
    patch := Q
    cap_direction := hcapdir
    cap_path := hcpath
    opposite_cap := ?_
    cap_contact := ?_
    patch_contact := ?_
    opposite_patch := fun e i => ((hmatched e).2 i).2.2
    matched_cut := hcut
    caps_patch_disjoint := ?_
    chains_disjoint := hseparated
    third_avoids := ?_
    covered := ?_ }⟩⟩
  · intro e i
    exact (disjoint_left.mpr fun _ hp => hother e i hp).symm
  · intro e i
    cases e <;> exact ((hmatched _).2 i).1
  · intro e i
    cases e <;> exact ((hmatched _).2 i).2.1
  · intro e f
    exact disjoint_left.mpr fun _ hpC hpQ =>
      hPavoid f (hQsub f hpQ) (Or.inl (hCunion e hpC))
  · apply disjoint_left.mpr
    intro p hpS hp
    obtain ⟨e, hp⟩ := mem_iUnion.mp hp
    rcases hp with hpE | hpQ
    · cases e
      · exact hthird hpS (Or.inl hpE)
      · exact hthird hpS (Or.inr hpE)
    · exact hPavoid e (hQsub e hpQ) (Or.inr hpS)
  · intro e p hp
    cases e
    · rcases lt_trichotomy p (b false) with hlt | heq | hgt
      · exact hcapSide false p ⟨hp.1, hlt⟩
      · simpa only [heq] using hattachment false
      · exact hpatchSide false p ⟨hgt, hp.2⟩
    · rcases lt_trichotomy p (b true) with hlt | heq | hgt
      · exact hpatchSide true p ⟨hp.1, hlt⟩
      · simpa only [heq] using hattachment true
      · exact hcapSide true p ⟨hgt, hp.2⟩

end PoincareConjecture
