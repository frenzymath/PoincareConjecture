import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcJoinedCollar
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThirdArcChain

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Matrix
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

structure M64IntrinsicThreeArcCollar
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) (b : Bool → ℝ) where
  joined : M64IntrinsicJoinedArcCollar C b
  reversed : Bool
  third : M64IntrinsicArcBandChain (fun t => sigma (if reversed then S - t else t))
    (C.radius (if reversed then true else false))
    (S - C.radius (if reversed then false else true)) U
  separated : ∀ i, Disjoint (third.band i).carrier
    (m64IntrinsicJoinedBandUnion joined.chain joined.patch)
  cap_contact : ∀ i, (C.carrier false ∪ C.carrier true) ∩ (third.band i).carrier =
    (if third.cut i.castSucc = C.radius (if reversed then true else false)
      then (third.band i).leftCut else ∅) ∪
    (if third.cut i.succ = S - C.radius (if reversed then false else true)
      then (third.band i).rightCut else ∅)
  third_covered : ∀ p ∈ Icc (0 : ℝ) S,
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ sigma p ∈ W ∧
      W ∩ closure U ⊆ (C.carrier false ∪ C.carrier true) ∪ ⋃ i, (third.band i).carrier

namespace M64IntrinsicThreeArcCollar

variable {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
  {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
  (D : M64IntrinsicThreeArcCollar C b)

abbrev carrier : Set AnnulusCoordinates :=
  ((C.carrier false ∪ C.carrier true) ∪
    m64IntrinsicJoinedBandUnion D.joined.chain D.joined.patch) ∪ ⋃ i, (D.third.band i).carrier

theorem isClosed_carrier : IsClosed D.carrier :=
  (((C.compact false).isClosed.union (C.compact true).isClosed).union
    D.joined.bands_closed).union
      (isClosed_iUnion_of_finite fun i => (D.third.band i).isClosed_carrier)

theorem occupied : D.carrier ⊆ closure U :=
  union_subset D.joined.occupied (iUnion_subset D.third.occupied)

theorem boundary_covered
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) :
    ∀ p ∈ frontier U, ∃ W : Set AnnulusCoordinates, IsOpen W ∧ p ∈ W ∧
      W ∩ closure U ⊆ D.carrier := by
  intro p hp
  rw [hfront] at hp
  rcases hp with ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
  · obtain ⟨W, hW, hpW, hcov⟩ := D.joined.covered false t ht
    exact ⟨W, hW, hpW, hcov.trans subset_union_left⟩
  · obtain ⟨W, hW, hpW, hcov⟩ := D.joined.covered true t ht
    exact ⟨W, hW, hpW, hcov.trans subset_union_left⟩
  · obtain ⟨W, hW, hpW, hcov⟩ := D.third_covered t ht
    exact ⟨W, hW, hpW, hcov.trans (union_subset
      (subset_union_left.trans subset_union_left) subset_union_right)⟩

end M64IntrinsicThreeArcCollar

theorem m64Intrinsic_extend_joined_collar
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T b : Bool → ℝ} {S : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hsi : InjOn sigma (Icc 0 S))
    (hsreg : ∀ t ∈ Ioo (0 : ℝ) S, deriv sigma t ≠ 0)
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) (J : M64IntrinsicJoinedArcCollar C b) :
    Nonempty (M64IntrinsicThreeArcCollar C b) := by
  have hfront' : frontier U = sigma '' Icc 0 S ∪
      (gamma false '' Icc 0 (T false) ∪ gamma true '' Icc 0 (T true)) :=
    hfront.trans (union_comm _ _)
  have havoid (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
      sigma t ∉ gamma false '' Icc 0 (T false) ∪ gamma true '' Icc 0 (T true) := by
    rintro (⟨x, hx, he⟩ | ⟨x, hx, he⟩)
    · exact ht.1.ne' (has x hx t (Ioo_subset_Icc_self ht) he).2
    · exact ht.2.ne (hbs x hx t (Ioo_subset_Icc_self ht) he).2
  have hrS (e : Bool) : C.radius e ≤ S / 3 := (C.radius_bound e).trans
    (div_le_div_of_nonneg_right (min_le_right (T e) S) (by norm_num))
  have hrT (e : Bool) : C.radius e ≤ T e := by
    have h := (C.radius_bound e).trans
      (div_le_div_of_nonneg_right (min_le_left (T e) S) (by norm_num : (0 : ℝ) ≤ 3))
    have hT := (J.attachment e).1.trans (J.attachment e).2
    linarith
  have htip (e : Bool) : ((0 : ℝ), C.radius e) ∈ (C.chart e).source := by
    simpa only [sectorParameterEquiv_apply, if_true, Prod.fst_zero, Prod.snd_zero,
      zero_add, one_mul, add_zero] using
      (C.axes_source e (true, true) (C.radius e) ⟨(C.radius_pos e).le, le_rfl⟩).2
  have hnear (e : Bool) :
      (fun s => gamma e (if e then T e - s else s)) '' Icc 0 (C.radius e) ⊆
        gamma false '' Icc 0 (T false) ∪ gamma true '' Icc 0 (T true) := by
    rintro p ⟨s, hs, rfl⟩
    cases e
    · exact Or.inl ⟨s, ⟨hs.1, hs.2.trans (hrT false)⟩, rfl⟩
    · apply Or.inr
      refine ⟨T true - s, ?_, rfl⟩
      constructor <;> linarith [hs.1, hs.2, hrT true]
  have hCfront (e : Bool) : C.carrier e ∩ frontier U ⊆
      (fun s => sigma (if e then S - s else s)) '' Icc 0 (C.radius e) ∪
        (gamma false '' Icc 0 (T false) ∪ gamma true '' Icc 0 (T true)) := by
    intro p hp
    rcases (C.frontier_contact e).subset hp with h | h
    · exact Or.inr (hnear e h)
    · exact Or.inl h
  have hcorner (e : Bool) : ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      sigma (if e then S else 0) ∈ W ∧ W ∩ closure U ⊆ C.carrier e := by
    refine ⟨C.neighborhood e, C.neighborhood_open e, ?_, C.covers_corner e⟩
    cases e
    · change sigma 0 ∈ C.neighborhood false
      rw [hstart]
      exact C.base_mem false
    · change sigma S ∈ C.neighborhood true
      rw [hend]
      exact C.base_mem true
  obtain ⟨reversed, E, hsep, hcontact, hcover⟩ := m64Intrinsic_exists_third_arc_chain
    hs hsi hsreg ((isCompact_Icc.image (hg false).continuous).union
      (isCompact_Icc.image (hg true).continuous)) havoid hU hV hUV hfront' hfV
    J.bands_closed J.third_avoids C.radius C.radius_pos hrS C.chart C.cap C.positive
    (fun e i => ⟨C.cap_source e i, C.cap_smooth e i, C.cap_inverse_smooth e i,
      C.cap_first e i, C.cap_second e i, C.cap_chord e i, C.cap_sector e i⟩)
    C.second_axis htip C.occupied C.separated hCfront hcorner
  exact ⟨{
    joined := J
    reversed := reversed
    third := E
    separated := hsep
    cap_contact := hcontact
    third_covered := hcover }⟩

theorem m64Intrinsic_exists_three_arc_collar
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
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
    (hsreg : ∀ t ∈ Ioo (0 : ℝ) S, deriv sigma t ≠ 0)
    (hind0 : LinearIndependent ℝ
      (![deriv (gamma false) 0, deriv sigma 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv (gamma true) (T true), -deriv sigma S] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (hray : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma e t + z • quarterTurn (deriv (gamma e) t) ∈ U) :
    ∃ C : M64IntrinsicThreeArcCaps gamma sigma T S U,
      ∃ b : Bool → ℝ, Nonempty (M64IntrinsicThreeArcCollar C b) := by
  obtain ⟨C⟩ := m64Intrinsic_exists_three_arc_cap_data gamma sigma T hg hs hT hS hinj hsi
    hstart hend hab hind0 hind1 hU hV hUV hfront hfV
  obtain ⟨b, ⟨J⟩⟩ := m64Intrinsic_exists_three_arc_joined_collar gamma sigma T hg
    hs.continuous hT hS hspeed hinj hjoin hreg htan hab has hbs hregular hU hV hUV hfront hfV hray C
  exact ⟨C, b, m64Intrinsic_extend_joined_collar hg hs hsi hsreg hstart hend has hbs
    hU hV hUV hfront hfV C J⟩

end PoincareConjecture
