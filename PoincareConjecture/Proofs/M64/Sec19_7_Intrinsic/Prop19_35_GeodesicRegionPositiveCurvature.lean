import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicRegionCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerActual
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapBandGluing












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_geodesic_return_region_curvature_ge_pi
    {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
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
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hcover : (⋃ i, (face i).carrier) = closure U) :
    Real.pi ≤ ∫ x in closure U, D.scalarCurvature x / 2 ∂g.volumeMeasure := by
  classical
  have hp : gamma 0 ∈ closure U := frontier_subset_closure (by
    rw [hfU]
    exact ⟨0, ⟨le_rfl, hT.le⟩, rfl⟩)
  obtain ⟨i, _⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
  let _ : Nonempty I := ⟨i⟩
  have heuler := m64Intrinsic_region_euler_ge_one_of_coordinate_triangulation
    face F b hsource hcarrier hboundary hfront hinter hU hV hdisj
      (hfU.trans hfV.symm) hclosure hcover hVconn
  have heulerR : (1 : ℝ) ≤ (Nat.card (Euler.CoordinateVertex F b) : ℝ) -
      Nat.card (FaceBoundaryEdge face) + Nat.card I := by exact_mod_cast heuler
  have hinj (i : I) (k : Fin 3) : InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1) :=
    m64Intrinsic_coordinate_face_boundary_injective (face i) (F i) (b i)
      (hsource i) (hboundary i) k
  have hcurvature := m64Intrinsic_geodesic_return_region_curvature_lower_bound
    face F b hF hFi hsource hcarrier hboundary hinj hinter hfront D hg hT hend hginj
      hgeo hunit hU hV hdisj hfU hfV hcover
  nlinarith [Real.pi_pos]

end PoincareConjecture
