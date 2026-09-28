import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConcreteArcBandChain





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture






theorem m64Intrinsic_exists_small_cap_patch_chain
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T r b delta : ℝ}
    (hr : 0 < r) (hrT : r < T) (hb : b ∈ Ioo (0 : ℝ) T) (hdelta : 0 < delta)
    (terminal : Bool) (hgap : (if terminal then b else r) < if terminal then T - r else b)
    (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V Z O : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoidK : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive vertical : Bool)
    (hsource : ∀ i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (F i).source)
    (hFi : ∀ i, ContDiffOn ℝ ∞ (F i).symm (F i).target)
    (hfirst : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hchord : ∀ i, ∀ t : ℝ, F i ((1 - t) * r, t * r) =
      (1 - t) • F i (r, 0) + t • F i (0, r))
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxis : ∀ s : ℝ, H (if vertical then (0, s) else (s, 0)) =
      gamma (if terminal then T - s else s))
    (htip : (if vertical then ((0 : ℝ), r) else (r, 0)) ∈ H.source)
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f : ℝ → ℝ} {a0 a1 ua wa ub wb ra rb : ℝ} (ha01 : a0 < a1)
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a0 a1 ua wa ub wb ra rb)
    (hbase : L (if terminal then a1 else a0, f (if terminal then a1 else a0)) = gamma b)
    (htangent : ∃ speed : ℝ, 0 < speed ∧
      deriv gamma b = speed • L (1, deriv f (if terminal then a1 else a0)))
    (htrans : 0 < inner ℝ (quarterTurn (deriv gamma b))
      (if terminal then L (ub, wb) else L (ua, wa)))
    (hlower : B.lowerArc = if terminal then gamma '' Icc 0 b else gamma '' Icc b T)
    (hBopen : B.carrier \ B.lowerArc ⊆ U)
    (hZ : IsClosed Z) (hZfront : Z ∩ frontier U ⊆ K)
    (hO : IsOpen O)
    (haxisO : gamma '' Icc (if terminal then b else r) (if terminal then T - r else b) ⊆ O) :
    let selected := if vertical then (positive, true) else (true, positive)
    let vC := if vertical then F selected (r, 0) - F selected (0, r)
      else F selected (0, r) - F selected (r, 0)
    let rho := if terminal then rb else ra
    let w := if terminal then L (ub, wb) else L (ua, wa)
    let C := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    let P := B.carrier ∪ Z
    C ⊆ closure U → Disjoint C P →
    C ∩ frontier U ⊆ (fun s => gamma (if terminal then T - s else s)) '' Icc 0 r ∪ K →
    (∃ W : Set AnnulusCoordinates, IsOpen W ∧
      gamma (if terminal then T else 0) ∈ W ∧ W ∩ closure U ⊆ C) →
    ∃ E : M64IntrinsicArcBandChain gamma
        (if terminal then b else r) (if terminal then T - r else b) U,
      E.length ≤ 1 ∧ E.length * rho < delta ∧
      E.direction (if terminal then T - r else r) = vC ∧ E.direction b = rho • w ∧
      (∀ z ∈ Icc (0 : ℝ) 1, gamma (if terminal then T - r else r) +
        z • E.direction (if terminal then T - r else r) ∈ C) ∧
      (∀ z ∈ Icc (0 : ℝ) 1, gamma b + z • E.direction b ∈ P) ∧
      (∀ i, (E.band i).carrier ⊆ O) ∧
      (∀ i, (C ∪ P) ∩ (E.band i).carrier =
        (if E.cut i.castSucc = (if terminal then b else r) then (E.band i).leftCut else ∅) ∪
          (if E.cut i.succ = (if terminal then T - r else b) then (E.band i).rightCut else ∅)) ∧
      ∀ p ∈ (if terminal then Ioc b T else Ico 0 b),
        ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧
          W ∩ closure U ⊆ C ∪ ⋃ i, (E.band i).carrier := by
  intro selected vC rho w C P hCsub hCP hCfront hcorner
  obtain ⟨d, hdC, hdP, hpathC, hpathP, n, c, R, G, g,
      hn, hmono, hfirstCut, hlastCut, epsilon, hepsilon, he1, hbands⟩ :=
    m64Intrinsic_exists_cap_patch_arc_bands hg hr hrT hb terminal hgap hinj hregular
      hK havoidK hU hV hUV hfront hfV hray H F positive vertical hsource hF hFi
      hfirst hsecond hchord hsector haxis htip L ha01 B hbase htangent htrans
      hlower hBopen hZ hZfront hO haxisO hCsub hCP hCfront hcorner
  have hrho : 0 < rho := by
    cases terminal
    · exact B.left_length_pos
    · exact B.right_length_pos
  let ell := min epsilon (delta / rho) / 2
  have hmin : 0 < min epsilon (delta / rho) := lt_min hepsilon (div_pos hdelta hrho)
  have hell : 0 < ell := half_pos hmin
  have hellE : ell < epsilon := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hellD : ell * rho < delta :=
    (lt_div_iff₀ hrho).mp ((half_lt_self hmin).trans_le (min_le_right _ _))
  obtain ⟨bands, hbandsO, hgeometry, hsep, hadj, hcontact, hcover⟩ :=
    hbands (fun _ => ell) (fun _ => ⟨hell, hellE⟩)
  let E : M64IntrinsicArcBandChain gamma
      (if terminal then b else r) (if terminal then T - r else b) U :=
    { count := n
      count_pos := hn
      cut := c
      cut_strictMono := hmono
      first_cut := hfirstCut
      last_cut := hlastCut
      direction := d
      frame := R
      parameter := G
      graph := g
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
  exact ⟨E, hellE.le.trans he1, hellD, hdC, hdP, hpathC, hpathP,
    hbandsO, hcontact, hcover⟩

end PoincareConjecture
