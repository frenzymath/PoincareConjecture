import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConcreteArcBandChain
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerOrientedBands





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_third_arc_chain
    {sigma : ℝ → AnnulusCoordinates} (hs : ContDiff ℝ ∞ sigma) {T : ℝ}
    (hinj : InjOn sigma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv sigma t ≠ 0)
    {K U V Z : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) T, sigma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = sigma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (hZ : IsClosed Z) (havoidZ : Disjoint (sigma '' Icc 0 T) Z)
    (r : Bool → ℝ) (hr : ∀ e, 0 < r e) (hrbound : ∀ e, r e ≤ T / 3)
    (H : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive : Bool → Bool)
    (hcap : ∀ e i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ (F e i).source ∧
      ContDiffOn ℝ ∞ (F e i) (F e i).source ∧
      ContDiffOn ℝ ∞ (F e i).symm (F e i).target ∧
      (∀ s ∈ Icc (0 : ℝ) (r e), F e i (s, 0) = H e (sectorParameterEquiv 0 i (s, 0))) ∧
      (∀ s ∈ Icc (0 : ℝ) (r e), F e i (0, s) = H e (sectorParameterEquiv 0 i (0, s))) ∧
      (∀ t : ℝ, F e i ((1 - t) * r e, t * r e) =
        (1 - t) • F e i (r e, 0) + t • F e i (0, r e)) ∧
      F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆
        H e '' ((H e).source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxis : ∀ (e : Bool) (s : ℝ), H e (0, s) = sigma (if e then T - s else s))
    (htip : ∀ e, ((0 : ℝ), r e) ∈ (H e).source) :
    let C (e : Bool) := ⋃ i,
      ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
    (∀ e, C e ⊆ closure U) → Disjoint (C false) (C true) →
    (∀ e : Bool, C e ∩ frontier U ⊆
      (fun s => sigma (if e then T - s else s)) '' Icc 0 (r e) ∪ K) →
    (∀ e : Bool, ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      sigma (if e then T else 0) ∈ W ∧ W ∩ closure U ⊆ C e) →
    ∃ reversed : Bool,
      let g : ℝ → AnnulusCoordinates := fun t => sigma (if reversed then T - t else t)
      let r' (e : Bool) := r (if reversed then !e else e)
      ∃ E : M64IntrinsicArcBandChain g (r' false) (T - r' true) U,
        (∀ i, Disjoint (E.band i).carrier Z) ∧
        (∀ i, (C false ∪ C true) ∩ (E.band i).carrier =
          (if E.cut i.castSucc = r' false then (E.band i).leftCut else ∅) ∪
            (if E.cut i.succ = T - r' true then (E.band i).rightCut else ∅)) ∧
        ∀ p ∈ Icc (0 : ℝ) T, ∃ W : Set AnnulusCoordinates, IsOpen W ∧ sigma p ∈ W ∧
          W ∩ closure U ⊆ (C false ∪ C true) ∪ ⋃ i, (E.band i).carrier := by
  intro C hCsub hCC hCfront hcorner
  obtain ⟨reversed, d, n, c, L, G, f, ell, hn, hmono, hfirst, hlast, hell,
      bands, hbandsO, hgeometry, hsep, hadj, hcontact, hcover⟩ :=
    m64Intrinsic_exists_two_corner_oriented_arc_bands hs hinj hregular hK havoid
      hU hV hUV hfront hfV r hr hrbound H F positive (fun _ => true)
      (fun e i => (hcap e i).1) (fun e i => (hcap e i).2.1)
      (fun e i => (hcap e i).2.2.1) (fun e i => (hcap e i).2.2.2.1)
      (fun e i => (hcap e i).2.2.2.2.1) (fun e i => (hcap e i).2.2.2.2.2.1)
      (fun e i => (hcap e i).2.2.2.2.2.2) haxis htip hZ.isOpen_compl
      (fun _ hp => disjoint_left.mp havoidZ hp) hCsub hCC hCfront hcorner
  let g : ℝ → AnnulusCoordinates := fun t => sigma (if reversed then T - t else t)
  let r' (e : Bool) := r (if reversed then !e else e)
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
  refine ⟨reversed, E, fun i => disjoint_left.mpr (fun _ hp => hbandsO i hp), hcontact, ?_⟩
  intro p hp
  have hparam : (if reversed then T - p else p) ∈ Icc (0 : ℝ) T := by
    cases reversed
    · exact hp
    · change T - p ∈ Icc (0 : ℝ) T
      constructor <;> linarith [hp.1, hp.2]
  obtain ⟨W, hW, hpW, hcov⟩ := hcover _ hparam
  refine ⟨W, hW, ?_, hcov⟩
  cases reversed
  · exact hpW
  · simpa only [if_true, sub_sub_cancel] using hpW

end PoincareConjecture
