import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBoundaryDegree














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

open Classical in






theorem m64Intrinsic_region_gaussBonnet_boundary_defects
    {I : Type*} [Fintype I] (face : I → SmoothFace AnnulusCoordinates)
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
      ∃ v : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i v)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (hgamma : ContinuousOn gamma (Icc 0 T)) (hend : gamma 0 = gamma T)
    (hginj : InjOn gamma (Ico 0 T))
    (htrace : frontier (⋃ i, (face i).carrier) = gamma '' Icc 0 T)
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart (F i) (b i))) :
    let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∫ x in ⋃ i, (face i).carrier, D.scalarCurvature x ∂g.volumeMeasure) +
      2 * (∑ p : I × Fin 3, if ∀ q : I × Fin 3,
          faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
        coordinateTriangleTurningIntegral D (F p.1) (b p.1) (Q p.1) (p.2 + 1) ((p.2 + 1) + 1)
        else 0) +
      2 * (∑ v : Euler.CoordinateVertex F b,
        ((if v.1 ∈ gamma '' Icc 0 T then Real.pi else 2 * Real.pi) -
          coordinateVertexAngleContribution g F b v.1)) =
      4 * Real.pi * ((Nat.card (Euler.CoordinateVertex F b) : ℝ) -
        Nat.card (FaceBoundaryEdge face) + Nat.card I) := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  let degree (v : Euler.CoordinateVertex F b) := Nat.card
    {e : {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
        faceBoundaryIndex face p.1 p.2 = e} = 1} //
      (Euler.coordinateEdgeEnds face F b e.1).1 = v ∨
        (Euler.coordinateEdgeEnds face F b e.1).2 = v}
  have hcoefficient (v : Euler.CoordinateVertex F b) :
      (2 - (degree v : ℝ) / 2) * Real.pi =
        if v.1 ∈ gamma '' Icc 0 T then Real.pi else 2 * Real.pi := by
    by_cases hv : v.1 ∈ gamma '' Icc 0 T
    · have hdegree : degree v = 2 :=
        m64Intrinsic_return_region_boundary_vertex_degree_two face F b hsource hcarrier
          hboundary hinter hfront hT hgamma hend hginj htrace v (htrace.symm ▸ hv)
      norm_num [hdegree, hv]
    · have hvregion : v.1 ∈ ⋃ i, (face i).carrier := by
        obtain ⟨⟨i, k⟩, hik⟩ := v.2
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        rw [hcarrier]
        exact ⟨b i k, subset_convexHull ℝ _ (mem_range_self k), hik⟩
      have hvint : v.1 ∈ interior (⋃ i, (face i).carrier) := by
        by_contra h
        exact hv (htrace ▸ ⟨subset_closure hvregion, h⟩)
      have hdegree : degree v = 0 :=
        m64Intrinsic_interior_vertex_boundary_degree_zero face F b hsource hboundary hinter v hvint
      norm_num [hdegree, hv]
  have hgb := m64Intrinsic_region_gaussBonnet_euler face F b hF hFi hsource hcarrier
    hboundary hfront D Q
  change _ + 2 * (∑ v : Euler.CoordinateVertex F b,
    ((2 - (degree v : ℝ) / 2) * Real.pi - coordinateVertexAngleContribution g F b v.1)) = _ at hgb
  simp_rw [hcoefficient] at hgb
  exact hgb

end PoincareConjecture
