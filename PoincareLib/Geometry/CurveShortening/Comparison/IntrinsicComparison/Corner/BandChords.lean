import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Cap.BandChords

/-! Actual exposed-corner contacts against bands on either incident arc.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareMT

/-- The actual outer-cut and positive-axis contacts force each retained corner-band contact
onto that cap's own chord. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481,
especially the regional Gauss--Bonnet argument of Lemma 19.45, p. 474; the explicit
coordinate construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-contacts.md`, Mathematical Checks. -/
theorem m64Intrinsic_retained_corner_band_inter_subset_chord
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 < r)
    (face : Bool × Bool → SmoothFace AnnulusCoordinates) (positive : Bool)
    (hsource : (r, 0) ∈ H.source ∧ (0, r) ∈ H.source)
    (hsub : ∀ i, (face i).carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsecond : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 1).map t =
      H (sectorParameterEquiv 0 i (0, t * r)))
    (hfirst : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 2).map t =
      H (sectorParameterEquiv 0 i (t * r, 0)))
    (hchord : ∀ i t, ((face i).boundary 0).map t =
      (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
        t • H (sectorParameterEquiv 0 i (0, r)))
    (hcoordinates : ∀ i, ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
      (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      convexHull ℝ (range b) ⊆ C.source ∧
      (face i).carrier = C '' convexHull ℝ (range b) ∧
      ∀ k, ((face i).boundary k).map = C ∘
        affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)))
    {G : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces G lo a b ua wa ub wb ra rb)
    {U K : Set AnnulusCoordinates} (hdisj : Disjoint U K)
    (hregion : B.carrier \ B.lowerArc ⊆ U) :
    let axes := (fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
      (fun t : ℝ => H (t * r, 0)) '' Icc 0 1
    let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
    let A := ⋃ i, ⋃ (_ : occupied i), (face i).carrier
    axes ⊆ K → axes ∩ B.lowerArc ⊆ {H (r, 0), H (0, r)} →
    A ∩ B.carrier ⊆ B.leftCut ∪ B.rightCut →
    ∀ i, occupied i → (face i).carrier ∩ B.carrier ⊆
      ((face i).boundary 0).map '' Icc (0 : ℝ) 1 := by
  classical
  intro axes occupied A haxes htip hinter i hi x hx
  have hxA : x ∈ A := mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hx.1⟩⟩
  have hxfront : x ∈ frontier A :=
    m64Intrinsic_band_cap_inter_subset_frontier B (Subset.refl A) hinter ⟨hxA, hx.2⟩
  rcases m64Intrinsic_retained_cap_exposed_chord H r face positive
      hsub hsecond hfirst hchord hcoordinates i hi ⟨hxfront, hx.1⟩ with haxis | hchord
  · have hxlower : x ∈ B.lowerArc := by
      by_contra hn
      exact disjoint_left.mp hdisj (hregion ⟨hx.2, hn⟩) (haxes haxis)
    exact m64Intrinsic_cap_positive_tip_on_chord H hr (face i) i (hsub i)
      (hchord i) hsource ⟨htip ⟨haxis, hxlower⟩, hx.1⟩
  · exact hchord

end PoincareMT
