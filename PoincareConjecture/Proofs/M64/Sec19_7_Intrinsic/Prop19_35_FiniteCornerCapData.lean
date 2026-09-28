import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapData

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

structure M64IntrinsicFiniteCornerCaps {J : Type*}
    (alpha beta : J → ℝ → AnnulusCoordinates) (A B : J → ℝ)
    (U : Set AnnulusCoordinates) where
  chart : J → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates
  radius : J → ℝ
  cap : J → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates
  neighborhood : J → Set AnnulusCoordinates
  positive : J → Bool
  radius_pos : ∀ j, 0 < radius j
  radius_bound : ∀ j, radius j ≤ min (A j) (B j) / 3
  zero_source : ∀ j, (0 : ℝ × ℝ) ∈ (chart j).source
  base : ∀ j, chart j 0 = alpha j 0
  smooth : ∀ j, ContDiffOn ℝ ∞ (chart j) (chart j).source
  inverse_smooth : ∀ j, ContDiffOn ℝ ∞ (chart j).symm (chart j).target
  first_axis : ∀ j (s : ℝ), chart j (s, 0) = alpha j s
  second_axis : ∀ j (s : ℝ), chart j (0, s) = beta j s
  axes_source : ∀ j (i : Bool × Bool), ∀ s ∈ Icc (0 : ℝ) (radius j),
    sectorParameterEquiv 0 i (s, 0) ∈ (chart j).source ∧
      sectorParameterEquiv 0 i (0, s) ∈ (chart j).source
  frontier_coordinates : ∀ j, ∀ q ∈ (chart j).source, chart j q ∈ frontier U ↔
    (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)
  occupied_coordinates : ∀ j, ∀ q ∈ (chart j).source, chart j q ∈ closure U ↔
    if positive j then 0 ≤ q.1 ∧ 0 ≤ q.2 else q.1 ≤ 0 ∨ q.2 ≤ 0
  cap_source : ∀ j i,
    {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ radius j} ⊆ (cap j i).source
  cap_target : ∀ j i, (cap j i).target ⊆ (chart j).target
  cap_smooth : ∀ j i, ContDiffOn ℝ ∞ (cap j i) (cap j i).source
  cap_inverse_smooth : ∀ j i, ContDiffOn ℝ ∞ (cap j i).symm (cap j i).target
  cap_first : ∀ j i, ∀ s ∈ Icc (0 : ℝ) (radius j),
    cap j i (s, 0) = chart j (sectorParameterEquiv 0 i (s, 0))
  cap_second : ∀ j i, ∀ s ∈ Icc (0 : ℝ) (radius j),
    cap j i (0, s) = chart j (sectorParameterEquiv 0 i (0, s))
  cap_chord : ∀ j i (t : ℝ), cap j i ((1 - t) * radius j, t * radius j) =
    (1 - t) • cap j i (radius j, 0) + t • cap j i (0, radius j)
  cap_sector : ∀ j i,
    cap j i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ radius j} ⊆
      chart j '' ((chart j).source ∩ (sectorParameterEquiv 0 i) ''
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2})
  cap_axis_contact : ∀ j i,
    (cap j i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ radius j}) ∩
      chart j '' ((chart j).source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
        chart j '' ((sectorParameterEquiv 0 i) ''
          ((Icc (0 : ℝ) (radius j) ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) (radius j))))
  neighborhood_open : ∀ j, IsOpen (neighborhood j)
  base_mem : ∀ j, alpha j 0 ∈ neighborhood j
  compact : ∀ j, IsCompact (m64IntrinsicOccupiedCapFamily (cap j) (radius j) (positive j))
  occupied : ∀ j, m64IntrinsicOccupiedCapFamily (cap j) (radius j) (positive j) ⊆ closure U
  covers_corner : ∀ j, neighborhood j ∩ closure U ⊆
    m64IntrinsicOccupiedCapFamily (cap j) (radius j) (positive j)
  frontier_contact : ∀ j,
    m64IntrinsicOccupiedCapFamily (cap j) (radius j) (positive j) ∩ frontier U =
      alpha j '' Icc 0 (radius j) ∪ beta j '' Icc 0 (radius j)
  separated : Pairwise (fun j k => Disjoint
    (m64IntrinsicOccupiedCapFamily (cap j) (radius j) (positive j))
    (m64IntrinsicOccupiedCapFamily (cap k) (radius k) (positive k)))

namespace M64IntrinsicFiniteCornerCaps

abbrev carrier {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
    {U : Set AnnulusCoordinates} (C : M64IntrinsicFiniteCornerCaps alpha beta A B U)
    (j : J) : Set AnnulusCoordinates :=
  m64IntrinsicOccupiedCapFamily (C.cap j) (C.radius j) (C.positive j)

end M64IntrinsicFiniteCornerCaps

theorem m64Intrinsic_exists_finite_corner_cap_data
    {J : Type*} [Finite J] (alpha beta : J → ℝ → AnnulusCoordinates)
    (A B : J → ℝ) (K : J → Set AnnulusCoordinates)
    (ha : ∀ j, ContDiff ℝ ∞ (alpha j)) (hb : ∀ j, ContDiff ℝ ∞ (beta j))
    (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (hai : ∀ j, InjOn (alpha j) (Icc 0 (A j)))
    (hbi : ∀ j, InjOn (beta j) (Icc 0 (B j)))
    (hbase : ∀ j, beta j 0 = alpha j 0)
    (hind : ∀ j, LinearIndependent ℝ
      (![deriv (alpha j) 0, deriv (beta j) 0] : Fin 2 → AnnulusCoordinates))
    (hK : ∀ j, IsCompact (K j)) (hpK : ∀ j, alpha j 0 ∉ K j)
    (hdistinct : Function.Injective (fun j => alpha j 0))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : ∀ j, frontier U = alpha j '' Icc 0 (A j) ∪ beta j '' Icc 0 (B j) ∪ K j)
    (hfV : frontier V = frontier U) :
    Nonempty (M64IntrinsicFiniteCornerCaps alpha beta A B U) := by
  classical
  obtain ⟨H, r, F, W, positive, hdata, hsep⟩ :=
    m64Intrinsic_exists_disjoint_finite_corner_caps alpha beta A B K ha hb hA hB hai hbi
      hbase hind hK hpK hdistinct hU hV hdisj hfU hfV
  choose hr hrbound hzero hbaseH hH hHi haxis haxis' hsmall hf hc hFdata
    hW hpW hcompact hsub hcover hcontact using hdata
  exact ⟨{
    chart := H
    radius := r
    cap := F
    neighborhood := W
    positive := positive
    radius_pos := hr
    radius_bound := hrbound
    zero_source := hzero
    base := hbaseH
    smooth := hH
    inverse_smooth := hHi
    first_axis := haxis
    second_axis := haxis'
    axes_source := hsmall
    frontier_coordinates := hf
    occupied_coordinates := hc
    cap_source := fun j i => (hFdata j i).1
    cap_target := fun j i => (hFdata j i).2.1
    cap_smooth := fun j i => (hFdata j i).2.2.1
    cap_inverse_smooth := fun j i => (hFdata j i).2.2.2.1
    cap_first := fun j i => (hFdata j i).2.2.2.2.1
    cap_second := fun j i => (hFdata j i).2.2.2.2.2.1
    cap_chord := fun j i => (hFdata j i).2.2.2.2.2.2.1
    cap_sector := fun j i => (hFdata j i).2.2.2.2.2.2.2.1
    cap_axis_contact := fun j i => (hFdata j i).2.2.2.2.2.2.2.2
    neighborhood_open := hW
    base_mem := hpW
    compact := hcompact
    occupied := hsub
    covers_corner := hcover
    frontier_contact := hcontact
    separated := hsep }⟩

end PoincareConjecture
