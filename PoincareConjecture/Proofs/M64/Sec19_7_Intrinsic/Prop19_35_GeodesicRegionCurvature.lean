import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnRegionCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicSideTurning

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

open Classical in

theorem m64Intrinsic_geodesic_return_region_curvature_lower_bound
    {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
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
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ}
    (hT : 0 < T) (hend : gamma 0 = gamma T) (hginj : InjOn gamma (Ico 0 T))
    (hgeo : g.IsGeodesicOn gamma (Icc 0 T))
    (hunit : ∀ p ∈ Icc 0 T, g.inner (gamma p) (deriv gamma p) (deriv gamma p) = 1)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hcover : (⋃ i, (face i).carrier) = closure U) :
    2 * Real.pi * ((Nat.card (Euler.CoordinateVertex F b) : ℝ) -
        Nat.card (FaceBoundaryEdge face) + Nat.card I) - Real.pi ≤
      ∫ x in closure U, D.scalarCurvature x / 2 ∂g.volumeMeasure := by
  classical
  let _ := Fintype.ofFinite I
  let Q (i : I) := g.alignedChartFrame (coordinateTriangleChart (F i) (b i))
    (coordinateTriangleChart_smooth (F i) (b i) (hFi i))
    (coordinateTriangleChart_smooth_symm (F i) (b i) (hF i))
  have htrace : frontier (⋃ i, (face i).carrier) = gamma '' Icc 0 T := by
    rw [hcover, (m64Intrinsic_jordan_interior_closure hU hV hdisj (hfU.trans hfV.symm)).2, hfU]
  have himage (i : I) (k : Fin 3) :
      (fun t : ℝ => F i (AffineMap.lineMap (b i (k + 1)) (b i ((k + 1) + 1)) t)) ''
        Icc (0 : ℝ) 1 = ((face i).boundary k).map '' Icc (0 : ℝ) 1 := by
    rw [coordinateTriangle_cyclic_boundary_image, hboundary, image_comp]
    congr 1
    unfold affineSegment
    apply image_congr
    intro t _
    simp only [affineChartSegment, AffineMap.lineMap_apply_module]
    module
  have hturn : (∑ p : I × Fin 3, if ∀ q : I × Fin 3,
      faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
        coordinateTriangleTurningIntegral D (F p.1) (b p.1) (Q p.1)
          (p.2 + 1) ((p.2 + 1) + 1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with hp
    · apply m64Intrinsic_coordinate_side_geodesic_turning_eq_zero D (F p.1) (b p.1)
        (hF p.1) (hFi p.1) (hsource p.1) (Q p.1)
        (by have h (k : Fin 3) : k + 1 ≠ (k + 1) + 1 := by fin_cases k <;> decide
            exact h p.2) hg hgeo hend hginj hunit
      rw [himage, ← htrace]
      exact m64Intrinsic_unpaired_side_subset_region_frontier face F b hsource hboundary hinter p hp
    · rfl
  have hregular (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) T) : deriv gamma p ≠ 0 := by
    intro hz
    have hu := hunit p (Ioo_subset_Icc_self hp)
    simp only [hz, map_zero] at hu
    norm_num at hu
  simpa only [hturn, add_zero] using
    m64Intrinsic_return_region_curvature_turning_lower_bound face F b hF hFi hsource
      hcarrier hboundary hinj hinter hfront D Q hg hT hend hginj hregular hU hV hdisj hfU hfV hcover

end PoincareConjecture
