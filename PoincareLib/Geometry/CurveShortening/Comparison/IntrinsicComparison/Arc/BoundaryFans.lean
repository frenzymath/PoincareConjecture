import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Arc.DefiningFunction
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Regional.BoundaryFans

/-!
# The canonical fan on an actual regular boundary arc

A compact embedded arc and the remaining compact frontier construct the
regular defining function. Thus every marked interior point of that arc
has the exact pi contribution, even when the other boundary joins are
corners.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- A canonical triangulation vertex on a regular interior part of one actual boundary arc
has no corner defect. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481,
especially Claim 19.40, pp. 470-471; the explicit project tangent-fan derivation is reviewed
in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical Checks. -/
theorem m64Intrinsic_region_arc_boundary_fan
    {I : Type*} [Fintype I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {a b' p : ℝ}
    (hginj : InjOn gamma (Icc a b')) (hp : p ∈ Ioo a b') (hregular : deriv gamma p ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : gamma p ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc a b' ∪ K) (hfV : frontier V = frontier U)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (q : Euler.CoordinateVertex F b) (hq : q.1 = gamma p) :
    coordinateVertexAngleContribution g F b q.1 = Real.pi := by
  obtain ⟨phi, ell, hd, hzero, hell, hregion⟩ :=
    m64Intrinsic_exists_arc_defining_function hg hginj hp hregular hK hpK
      hU hV hdisj hfU hfV
  apply m64Intrinsic_regional_boundary_vertex_fan face F b hF hFi hsource hcarrier
    hboundary hinj hinter hfront g q (hq.symm ▸ hd) (hq.symm ▸ hzero) hell
  simpa only [hq, hcover] using hregion

end PoincareMT
