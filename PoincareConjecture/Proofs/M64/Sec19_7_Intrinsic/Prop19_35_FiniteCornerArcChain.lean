import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCapData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConcreteArcBandChain
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBandOppositeNeighborhood

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_finite_corner_arc_chain
    {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
    {U V K Z : Set AnnulusCoordinates}
    (C : M64IntrinsicFiniteCornerCaps alpha beta A B U)
    (corner : Bool → J) (hcorners : corner false ≠ corner true) (vertical : Bool → Bool)
    {sigma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hs : ContDiff ℝ ∞ sigma) (hinj : InjOn sigma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv sigma t ≠ 0)
    (hK : IsCompact K) (havoid : ∀ t ∈ Ioo (0 : ℝ) T, sigma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = sigma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (hZ : IsClosed Z) (havoidZ : Disjoint (sigma '' Icc 0 T) Z)
    (hrbound : ∀ e, C.radius (corner e) ≤ T / 3)
    (haxis : ∀ (e : Bool) (s : ℝ),
      C.chart (corner e) (if vertical e then (0, s) else (s, 0)) =
        sigma (if e then T - s else s))
    (hcapfront : ∀ e : Bool, C.carrier (corner e) ∩ frontier U ⊆
      (fun s => sigma (if e then T - s else s)) '' Icc 0 (C.radius (corner e)) ∪ K) :
    ∃ reversed : Bool,
      let g : ℝ → AnnulusCoordinates := fun t => sigma (if reversed then T - t else t)
      let r' (e : Bool) := C.radius (corner (if reversed then !e else e))
      ∃ E : M64IntrinsicArcBandChain g (r' false) (T - r' true) U,
        (∀ i, Disjoint (E.band i).carrier Z) ∧
        (∀ i, Disjoint (E.band i).carrier K) ∧
        (∀ i, (C.carrier (corner false) ∪ C.carrier (corner true)) ∩ (E.band i).carrier =
          (if E.cut i.castSucc = r' false then (E.band i).leftCut else ∅) ∪
            (if E.cut i.succ = T - r' true then (E.band i).rightCut else ∅)) ∧
        ∀ p ∈ Icc (0 : ℝ) T, ∃ W : Set AnnulusCoordinates, IsOpen W ∧ sigma p ∈ W ∧
          W ∩ closure U ⊆ (C.carrier (corner false) ∪ C.carrier (corner true)) ∪
            ⋃ i, (E.band i).carrier := by
  have htip (e : Bool) : (if vertical e then ((0 : ℝ), C.radius (corner e))
      else (C.radius (corner e), 0)) ∈ (C.chart (corner e)).source := by
    have hh := C.axes_source (corner e) (true, true) (C.radius (corner e))
      ⟨(C.radius_pos (corner e)).le, le_rfl⟩
    simp only [sectorParameterEquiv_apply, if_true, Prod.fst_zero, Prod.snd_zero, add_zero] at hh
    cases vertical e
    · exact hh.1
    · exact hh.2
  have hcorner (e : Bool) : ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      sigma (if e then T else 0) ∈ W ∧ W ∩ closure U ⊆ C.carrier (corner e) := by
    have hp : sigma (if e then T else 0) = alpha (corner e) 0 := by
      have h := haxis e 0
      have hz : (if vertical e then ((0 : ℝ), 0) else (0, 0)) = (0 : ℝ × ℝ) := by simp
      rw [hz, C.base] at h
      simpa only [sub_zero] using h.symm
    exact ⟨C.neighborhood (corner e), C.neighborhood_open (corner e),
      hp.symm ▸ C.base_mem (corner e), C.covers_corner (corner e)⟩
  obtain ⟨reversed, d, n, c, L, G, f, ell, hn, hmono, hfirst, hlast, hell,
      bands, hbandsO, hgeometry, hsep, hadj, hcontact, hcover⟩ :=
    m64Intrinsic_exists_two_corner_oriented_arc_bands hs hinj hregular hK havoid
      hU hV hUV hfront hfV (fun e => C.radius (corner e))
      (fun e => C.radius_pos (corner e)) hrbound (fun e => C.chart (corner e))
      (fun e => C.cap (corner e)) (fun e => C.positive (corner e)) vertical
      (fun e => C.cap_source (corner e)) (fun e => C.cap_smooth (corner e))
      (fun e => C.cap_inverse_smooth (corner e)) (fun e => C.cap_first (corner e))
      (fun e => C.cap_second (corner e)) (fun e => C.cap_chord (corner e))
      (fun e => C.cap_sector (corner e)) haxis htip hZ.isOpen_compl
      (fun _ hp => disjoint_left.mp havoidZ hp) (fun e => C.occupied (corner e))
      (C.separated hcorners) hcapfront hcorner
  let g : ℝ → AnnulusCoordinates := fun t => sigma (if reversed then T - t else t)
  let r' (e : Bool) := C.radius (corner (if reversed then !e else e))
  let E : M64IntrinsicArcBandChain g (r' false) (T - r' true) U :=
    { count := n
      count_pos := hn
      cut := c
      cut_strictMono := hmono
      first_cut := hfirst
      last_cut := hlast
      direction := d
      frame := L
      parameter := G
      graph := f
      length := ell
      length_pos := hell
      band := bands
      lower_arc := fun i => (hgeometry i).1
      left_cut := fun i => (hgeometry i).2.1
      right_cut := fun i => (hgeometry i).2.2.1
      occupied := fun i => (hgeometry i).2.2.2.1
      off_lower := fun i => (hgeometry i).2.2.2.2
      separated := hsep
      adjacent := hadj }
  have hlower (i : Fin E.count) : (E.band i).lowerArc ⊆ sigma '' Ioo 0 T := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := E.lower_subset i hp
    refine ⟨if reversed then T - t else t, ?_, rfl⟩
    have h0 : 0 < r' false := C.radius_pos _
    have h1 : 0 < r' true := C.radius_pos _
    cases reversed
    · change t ∈ Ioo 0 T
      exact ⟨h0.trans_le ht.1, by linarith only [h1, ht.2]⟩
    · change T - t ∈ Ioo 0 T
      constructor <;> linarith only [h0, h1, ht.1, ht.2]
  have havoid' : Disjoint (sigma '' Ioo 0 T) K := by
    apply disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩
    exact havoid t ht
  have hrest := (m64Intrinsic_arc_band_carriers_avoid_remainder
    (fun i => (E.band i).carrier) (fun i => (E.band i).lowerArc)
    (fun i => (E.band i).isClosed_carrier) hU hfront havoid' hlower E.off_lower).2
  refine ⟨reversed, E, fun i => disjoint_left.mpr (fun _ hp => hbandsO i hp),
    ?_, hcontact, ?_⟩
  · intro i
    exact disjoint_left.mpr (fun p hp hpk => hrest hpk (mem_iUnion.mpr ⟨i, hp⟩))
  · intro p hp
    have hparam : (if reversed then T - p else p) ∈ Icc (0 : ℝ) T := by
      cases reversed
      · exact hp
      · change T - p ∈ Icc 0 T
        constructor <;> linarith only [hp.1, hp.2]
    obtain ⟨W, hW, hpW, hcov⟩ := hcover _ hparam
    refine ⟨W, hW, ?_, hcov⟩
    cases reversed
    · exact hpW
    · simpa only [if_true, sub_sub_cancel] using hpW

end PoincareConjecture
