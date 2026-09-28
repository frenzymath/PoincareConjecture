import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopBoundaryFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalInteriorFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBoundaryEuler

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem coordinate_vertex_angle_nonneg
    {I : Type*} [Fintype I] (g : RiemannianMetric 2 AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates) (q : AnnulusCoordinates) :
    0 ≤ coordinateVertexAngleContribution g F b q := by
  unfold coordinateVertexAngleContribution
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact Real.arccos_nonneg _
  · exact le_rfl

open Classical in

theorem m64Intrinsic_return_region_curvature_turning_lower_bound
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
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart (F i) (b i)))
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ}
    (hT : 0 < T) (hend : gamma 0 = gamma T) (hginj : InjOn gamma (Ico 0 T))
    (hregular : ∀ p ∈ Ioo (0 : ℝ) T, deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hcover : (⋃ i, (face i).carrier) = closure U) :
    2 * Real.pi * ((Nat.card (Euler.CoordinateVertex F b) : ℝ) -
        Nat.card (FaceBoundaryEdge face) + Nat.card I) - Real.pi ≤
      (∫ x in closure U, D.scalarCurvature x / 2 ∂g.volumeMeasure) +
        ∑ p : I × Fin 3, if ∀ q : I × Fin 3,
            faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
          coordinateTriangleTurningIntegral D (F p.1) (b p.1) (Q p.1)
            (p.2 + 1) ((p.2 + 1) + 1)
          else 0 := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  let defect (v : Euler.CoordinateVertex F b) :=
    (if v.1 ∈ gamma '' Icc 0 T then Real.pi else 2 * Real.pi) -
      coordinateVertexAngleContribution g F b v.1
  have htrace : frontier (⋃ i, (face i).carrier) = gamma '' Icc 0 T := by
    rw [hcover, (m64Intrinsic_jordan_interior_closure hU hV hdisj (hfU.trans hfV.symm)).2, hfU]
  have hzero (v : Euler.CoordinateVertex F b) (hv : v.1 ≠ gamma 0) : defect v = 0 := by
    by_cases hboundaryv : v.1 ∈ gamma '' Icc 0 T
    · obtain ⟨p, hp, hpq⟩ := hboundaryv
      have hp0 : 0 < p := lt_of_le_of_ne hp.1 (by
        intro h
        apply hv
        simpa only [← h] using hpq.symm)
      have hpT : p < T := lt_of_le_of_ne hp.2 (by
        intro h
        apply hv
        exact hpq.symm.trans ((congrArg gamma h).trans hend.symm))
      have hfan := m64Intrinsic_return_region_smooth_boundary_fan face F b hF hFi hsource
        hcarrier hboundary hinj hinter hfront g hg hend hginj ⟨hp0, hpT⟩
        (hregular p ⟨hp0, hpT⟩) hU hV hdisj hfU hfV hcover v hpq.symm
      have hmem : v.1 ∈ gamma '' Icc 0 T := ⟨p, hp, hpq⟩
      simp only [defect, if_pos hmem, hfan, sub_self]
    · have hvregion : v.1 ∈ ⋃ i, (face i).carrier := by
        obtain ⟨⟨i, k⟩, hik⟩ := v.2
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        rw [hcarrier]
        exact ⟨b i k, subset_convexHull ℝ _ (mem_range_self k), hik⟩
      have hvint : v.1 ∈ interior (⋃ i, (face i).carrier) := by
        by_contra h
        exact hboundaryv (htrace ▸ ⟨subset_closure hvregion, h⟩)
      have hfan := m64Intrinsic_regional_interior_vertex_fan face F b hF hFi hsource
        hcarrier hboundary hinj hinter hfront g v hvint
      simp only [defect, if_neg hboundaryv, hfan, sub_self]
  have hdefect : (∑ v, defect v) ≤ Real.pi := by
    by_cases hex : ∃ v : Euler.CoordinateVertex F b, v.1 = gamma 0
    · obtain ⟨v, hv⟩ := hex
      rw [Finset.sum_eq_single v]
      · have hmem : v.1 ∈ gamma '' Icc 0 T := ⟨0, ⟨le_rfl, hT.le⟩, hv.symm⟩
        dsimp only [defect]
        rw [if_pos hmem]
        linarith [coordinate_vertex_angle_nonneg g F b v.1]
      · intro w _ hw
        apply hzero
        exact fun heq => hw (Subtype.ext (heq.trans hv.symm))
      · simp
    · have hsumzero : (∑ v, defect v) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        exact hzero v (fun hv => hex ⟨v, hv⟩)
      rw [hsumzero]
      exact Real.pi_pos.le
  have hgb := m64Intrinsic_region_gaussBonnet_boundary_defects face F b hF hFi hsource
    hcarrier hboundary hinter hfront hT hg.continuous.continuousOn hend hginj htrace D Q
  change _ + 2 * _ + 2 * (∑ v, defect v) = _ at hgb
  rw [hcover] at hgb
  rw [integral_div]
  linarith

end PoincareConjecture
