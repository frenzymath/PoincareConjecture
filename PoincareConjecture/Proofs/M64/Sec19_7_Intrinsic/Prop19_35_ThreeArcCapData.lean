import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCornerCaps

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

abbrev m64IntrinsicOccupiedCapFamily
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (r : ℝ) (positive : Bool) : Set AnnulusCoordinates :=
  ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}

structure M64IntrinsicThreeArcCaps (gamma : Bool → ℝ → AnnulusCoordinates)
    (sigma : ℝ → AnnulusCoordinates) (T : Bool → ℝ) (S : ℝ)
    (U : Set AnnulusCoordinates) where
  chart : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates
  radius : Bool → ℝ
  cap : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates
  neighborhood : Bool → Set AnnulusCoordinates
  positive : Bool → Bool
  radius_pos : ∀ e, 0 < radius e
  radius_bound : ∀ e, radius e ≤ min (T e) S / 3
  zero_source : ∀ e, (0 : ℝ × ℝ) ∈ (chart e).source
  base : ∀ e : Bool, chart e 0 = gamma e (if e then T e else 0)
  smooth : ∀ e, ContDiffOn ℝ ∞ (chart e) (chart e).source
  inverse_smooth : ∀ e, ContDiffOn ℝ ∞ (chart e).symm (chart e).target
  first_axis : ∀ (e : Bool) (s : ℝ), chart e (s, 0) = gamma e (if e then T e - s else s)
  second_axis : ∀ (e : Bool) (s : ℝ), chart e (0, s) = sigma (if e then S - s else s)
  axes_source : ∀ (e : Bool) (i : Bool × Bool), ∀ s ∈ Icc (0 : ℝ) (radius e),
    sectorParameterEquiv 0 i (s, 0) ∈ (chart e).source ∧
      sectorParameterEquiv 0 i (0, s) ∈ (chart e).source
  frontier_coordinates : ∀ e, ∀ q ∈ (chart e).source, chart e q ∈ frontier U ↔
    (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)
  occupied_coordinates : ∀ e, ∀ q ∈ (chart e).source, chart e q ∈ closure U ↔
    if positive e then 0 ≤ q.1 ∧ 0 ≤ q.2 else q.1 ≤ 0 ∨ q.2 ≤ 0
  cap_source : ∀ e i,
    {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ radius e} ⊆ (cap e i).source
  cap_target : ∀ e i, (cap e i).target ⊆ (chart e).target
  cap_smooth : ∀ e i, ContDiffOn ℝ ∞ (cap e i) (cap e i).source
  cap_inverse_smooth : ∀ e i, ContDiffOn ℝ ∞ (cap e i).symm (cap e i).target
  cap_first : ∀ e i, ∀ s ∈ Icc (0 : ℝ) (radius e),
    cap e i (s, 0) = chart e (sectorParameterEquiv 0 i (s, 0))
  cap_second : ∀ e i, ∀ s ∈ Icc (0 : ℝ) (radius e),
    cap e i (0, s) = chart e (sectorParameterEquiv 0 i (0, s))
  cap_chord : ∀ e i (t : ℝ), cap e i ((1 - t) * radius e, t * radius e) =
    (1 - t) • cap e i (radius e, 0) + t • cap e i (0, radius e)
  cap_sector : ∀ e i,
    cap e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ radius e} ⊆
      chart e '' ((chart e).source ∩ (sectorParameterEquiv 0 i) ''
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2})
  cap_axis_contact : ∀ e i,
    (cap e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ radius e}) ∩
      chart e '' ((chart e).source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
        chart e '' ((sectorParameterEquiv 0 i) ''
          ((Icc (0 : ℝ) (radius e) ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) (radius e))))
  neighborhood_open : ∀ e, IsOpen (neighborhood e)
  base_mem : ∀ e : Bool, gamma e (if e then T e else 0) ∈ neighborhood e
  compact : ∀ e, IsCompact (m64IntrinsicOccupiedCapFamily (cap e) (radius e) (positive e))
  occupied : ∀ e, m64IntrinsicOccupiedCapFamily (cap e) (radius e) (positive e) ⊆ closure U
  covers_corner : ∀ e, neighborhood e ∩ closure U ⊆
    m64IntrinsicOccupiedCapFamily (cap e) (radius e) (positive e)
  frontier_contact : ∀ e : Bool,
    m64IntrinsicOccupiedCapFamily (cap e) (radius e) (positive e) ∩ frontier U =
      (fun s => gamma e (if e then T e - s else s)) '' Icc 0 (radius e) ∪
        (fun s => sigma (if e then S - s else s)) '' Icc 0 (radius e)
  separated : Disjoint
    (m64IntrinsicOccupiedCapFamily (cap false) (radius false) (positive false))
    (m64IntrinsicOccupiedCapFamily (cap true) (radius true) (positive true))

namespace M64IntrinsicThreeArcCaps

abbrev carrier {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) (e : Bool) : Set AnnulusCoordinates :=
  m64IntrinsicOccupiedCapFamily (C.cap e) (C.radius e) (C.positive e)

end M64IntrinsicThreeArcCaps

theorem m64Intrinsic_exists_three_arc_cap_data
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (hind0 : LinearIndependent ℝ
      (![deriv (gamma false) 0, deriv sigma 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv (gamma true) (T true), -deriv sigma S] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U) : Nonempty (M64IntrinsicThreeArcCaps gamma sigma T S U) := by
  classical
  obtain ⟨H, r, F, W, positive, hdata, hsep⟩ := m64Intrinsic_exists_three_arc_corner_caps
    (hg false) (hg true) hs (hT false) (hT true) hS (hinj false) (hinj true) hsi
    hstart hend hab hind0 hind1 hU hV hUV hfront hfV
  choose hr hrbound hzero hbase hH hHi haxis haxis' hsmall hf hc hFdata
    hW hpW hcompact hsub hcover hcontact using hdata
  refine ⟨{
    chart := H
    radius := r
    cap := F
    neighborhood := W
    positive := positive
    radius_pos := hr
    radius_bound := ?_
    zero_source := hzero
    base := ?_
    smooth := hH
    inverse_smooth := hHi
    first_axis := ?_
    second_axis := haxis'
    axes_source := hsmall
    frontier_coordinates := hf
    occupied_coordinates := hc
    cap_source := fun e i => (hFdata e i).1
    cap_target := fun e i => (hFdata e i).2.1
    cap_smooth := fun e i => (hFdata e i).2.2.1
    cap_inverse_smooth := fun e i => (hFdata e i).2.2.2.1
    cap_first := fun e i => (hFdata e i).2.2.2.2.1
    cap_second := fun e i => (hFdata e i).2.2.2.2.2.1
    cap_chord := fun e i => (hFdata e i).2.2.2.2.2.2.1
    cap_sector := fun e i => (hFdata e i).2.2.2.2.2.2.2.1
    cap_axis_contact := fun e i => (hFdata e i).2.2.2.2.2.2.2.2
    neighborhood_open := hW
    base_mem := ?_
    compact := hcompact
    occupied := hsub
    covers_corner := hcover
    frontier_contact := ?_
    separated := hsep }⟩
  · intro e
    cases e <;> exact hrbound _
  · intro e
    cases e <;> exact hbase _
  · intro e s
    cases e <;> exact haxis _ s
  · intro e
    cases e <;> exact hpW _
  · intro e
    cases e <;> exact hcontact _

end PoincareConjecture
