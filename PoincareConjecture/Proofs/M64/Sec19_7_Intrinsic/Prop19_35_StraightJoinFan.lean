import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinDefiningFunction
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalBoundaryFans

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_straight_join_region_vertex_fan
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
    (g : RiemannianMetric 2 AnnulusCoordinates) (q : Euler.CoordinateVertex F b)
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a A B d c : ℝ} (haA : a < A) (hBd : B < d) (hc : 0 < c)
    (hai : InjOn alpha (Icc a A)) (hbi : InjOn beta (Icc B d))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha A ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = (alpha '' Icc a A ∪ beta '' Icc B d) ∪ K)
    (hfV : frontier V = frontier U)
    (hcover : (⋃ i, (face i).carrier) = closure U) (hq : q.1 = alpha A) :
    coordinateVertexAngleContribution g F b q.1 = Real.pi := by
  obtain ⟨phi, ell, hd, hz, hell, hregion⟩ :=
    m64Intrinsic_exists_straight_join_defining_function ha hb haA hBd hc hai hbi
      hend hreg htan hK hpK hU hV hdisj hfU hfV
  apply m64Intrinsic_regional_boundary_vertex_fan face F b hF hFi hsource
    hcarrier hboundary hinj hinter hfront g q (phi := phi) (ell := ell)
  · simpa only [hq] using hd
  · simpa only [hq] using hz
  · exact hell
  · simpa only [hq, hcover] using hregion

end PoincareConjecture
