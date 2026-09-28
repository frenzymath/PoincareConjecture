import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcLoop
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcFanDefects
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBoundaryEuler
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerActual
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionArcTurning
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcSideClassification
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCrossing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

open Classical in

theorem m64Intrinsic_two_arc_region_curvature_turning_ge_pi_div_two
    {I : Type*} [Fintype I] (N : IntrinsicAnnulus)
    (face : I → SmoothFace AnnulusCoordinates)
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
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame N.metric (coordinateTriangleChart (F i) (b i)))
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (ha0 : deriv alpha 0 ≠ 0)
    (hareg : ∀ p ∈ Ioo (0 : ℝ) A, deriv alpha p ≠ 0)
    (hbreg : ∀ p ∈ Ioo (0 : ℝ) B, deriv beta p ≠ 0)
    (horth : N.metric.inner (alpha 0) (deriv alpha 0) (deriv beta 0) = 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hnorm : ‖alpha 0‖ = 1) (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (v0 v1 : Euler.CoordinateVertex F b) (hv0 : v0.1 = alpha 0) (hv1 : v1.1 = alpha A) :
    Real.pi / 2 ≤
      (∫ x in closure U, N.connection.scalarCurvature x / 2 ∂N.metric.volumeMeasure) +
        ∑ p : I × Fin 3, if ∀ q : I × Fin 3,
            faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
          coordinateTriangleTurningIntegral N.connection (F p.1) (b p.1) (Q p.1)
            (p.2 + 1) ((p.2 + 1) + 1) else 0 := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  let _ : Nonempty I := by
    obtain ⟨⟨i, _⟩, _⟩ := v0.2
    exact ⟨i⟩
  obtain ⟨loop, hloop, hloopEnd, hloopInj, hloopImage⟩ :=
    m64Intrinsic_exists_simple_loop_between_arcs hA hB ha.continuous.continuousOn
      hb.continuous.continuousOn hai hbi hbase.symm hend.symm hmeet
  have htrace : frontier (⋃ i, (face i).carrier) = loop '' Icc (0 : ℝ) 2 := by
    rw [hcover, (m64Intrinsic_jordan_interior_closure hU hV hdisj hfV.symm).2, hfU, hloopImage]
  have hgb := m64Intrinsic_region_gaussBonnet_boundary_defects face F b hF hFi hsource
    hcarrier hboundary hinter hfront (by norm_num : (0 : ℝ) < 2)
    hloop hloopEnd hloopInj htrace N.connection Q
  have hcoefficient (v : Euler.CoordinateVertex F b) :
      (if v.1 ∈ loop '' Icc (0 : ℝ) 2 then Real.pi else 2 * Real.pi) =
        (if v.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B then Real.pi else 2 * Real.pi) := by
    by_cases hv : v.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B
    · have hvloop : v.1 ∈ loop '' Icc (0 : ℝ) 2 := by rwa [hloopImage]
      simp only [if_pos hvloop, if_pos hv]
    · have hvloop : v.1 ∉ loop '' Icc (0 : ℝ) 2 := by rwa [hloopImage]
      simp only [if_neg hvloop, if_neg hv]
  simp_rw [hcoefficient] at hgb
  rw [hcover] at hgb
  have hdefect := m64Intrinsic_two_arc_region_fan_defects_le face F b hF hFi hsource
    hcarrier hboundary hinj hinter hfront N.metric ha hb hA hB hai hbi hbase hend hmeet
    ha0 hareg hbreg horth hU hV hdisj hfU hfV hnorm hinward hsub hcover v0 v1 hv0 hv1
  have heuler := m64Intrinsic_region_euler_ge_one_of_coordinate_triangulation
    face F b hsource hcarrier hboundary hfront hinter hU hV hdisj hfV.symm
    hclosure hcover hVconn
  have heulerR : (1 : ℝ) ≤ (Nat.card (Euler.CoordinateVertex F b) : ℝ) -
      Nat.card (FaceBoundaryEdge face) + Nat.card I := by exact_mod_cast heuler
  have heulerPi := mul_le_mul_of_nonneg_left heulerR
    (show 0 ≤ 4 * Real.pi by positivity)
  dsimp only at hgb hdefect
  have htotal := heulerPi.trans_eq hgb.symm
  let curvature := ∫ x in closure U, N.connection.scalarCurvature x ∂N.metric.volumeMeasure
  let turning := ∑ p : I × Fin 3, if ∀ q : I × Fin 3,
      faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
    coordinateTriangleTurningIntegral N.connection (F p.1) (b p.1) (Q p.1)
      (p.2 + 1) ((p.2 + 1) + 1) else 0
  let defects := ∑ v : Euler.CoordinateVertex F b,
    ((if v.1 ∈ alpha '' Icc 0 A ∪ beta '' Icc 0 B then Real.pi else 2 * Real.pi) -
      coordinateVertexAngleContribution N.metric F b v.1)
  change 4 * Real.pi * 1 ≤ curvature + 2 * turning + 2 * defects at htotal
  change defects ≤ 3 * Real.pi / 2 at hdefect
  rw [integral_div]
  change Real.pi / 2 ≤ curvature / 2 + turning
  linarith only [htotal, hdefect]

theorem m64Intrinsic_circle_geodesic_region_curvature_lower_bound
    {I : Type*} [Finite I] (N : IntrinsicAnnulus)
    (face : I → SmoothFace AnnulusCoordinates)
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
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (ha0 : deriv alpha 0 ≠ 0)
    (hareg : ∀ p ∈ Ioo (0 : ℝ) A, deriv alpha p ≠ 0)
    (hgeo : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunit : ∀ p ∈ Icc 0 B,
      N.metric.inner (beta p) (deriv beta p) (deriv beta p) = 1)
    (horth : N.metric.inner (alpha 0) (deriv alpha 0) (deriv beta 0) = 0)
    {a b0 : ℝ} (hab : a ≤ b0)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b0))
    (hcircle : alpha '' Icc 0 A = intrinsicAnnulusBoundary 1 '' Icc a b0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (v0 v1 : Euler.CoordinateVertex F b) (hv0 : v0.1 = alpha 0) (hv1 : v1.1 = alpha A) :
    Real.pi / 2 - intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b0 ≤
      ∫ x in closure U, N.connection.scalarCurvature x / 2 ∂N.metric.volumeMeasure := by
  classical
  let _ := Fintype.ofFinite I
  let Q (i : I) := N.metric.alignedChartFrame (coordinateTriangleChart (F i) (b i))
    (coordinateTriangleChart_smooth (F i) (b i) (hFi i))
    (coordinateTriangleChart_smooth_symm (F i) (b i) (hF i))
  have hinj (i : I) (k : Fin 3) : InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1) :=
    m64Intrinsic_coordinate_boundary_injective face F b hsource hboundary i k
  have hnorm : ‖alpha 0‖ = 1 := by
    have hmem : alpha 0 ∈ intrinsicAnnulusBoundary 1 '' Icc a b0 := by
      rw [← hcircle]
      exact ⟨0, ⟨le_rfl, hA.le⟩, rfl⟩
    obtain ⟨s, _, hs⟩ := hmem
    rw [← hs, m64Intrinsic_inner_boundary_norm]
  have hbreg (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) B) : deriv beta p ≠ 0 := by
    intro hz
    have hu := hunit p (Ioo_subset_Icc_self hp)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hcurvature := m64Intrinsic_two_arc_region_curvature_turning_ge_pi_div_two
    N face F b hF hFi hsource hcarrier hboundary hinj hinter hfront Q ha hb hA hB
    hai hbi hbase hend hmeet ha0 hareg hbreg horth hU hV hdisj hfU hfV hclosure hVconn
    hnorm hinward hsub hcover v0 v1 hv0 hv1
  have htrace : frontier (⋃ i, (face i).carrier) =
      intrinsicAnnulusBoundary 1 '' Icc a b0 ∪ beta '' Icc 0 B := by
    rw [hcover, (m64Intrinsic_jordan_interior_closure hU hV hdisj hfV.symm).2, hfU, hcircle]
  have hmeetImages : (intrinsicAnnulusBoundary 1 '' Icc a b0) ∩
      (beta '' Icc 0 B) ⊆ {v0.1, v1.1} := by
    rw [← hcircle]
    rintro x ⟨⟨s, hs, hsx⟩, ⟨t, ht, htx⟩⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases hmeet s hs t ht (hsx.trans htx.symm) with h | h
    · exact Or.inl (hsx.symm.trans ((congrArg alpha h.1).trans hv0.symm))
    · exact Or.inr (hsx.symm.trans ((congrArg alpha h.1).trans hv1.symm))
  have hclass (p : I × Fin 3)
      (hp : ∀ q : I × Fin 3,
        faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p) :
      ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
        intrinsicAnnulusBoundary 1 '' Icc a b0 ∨
      ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ beta '' Icc 0 B := by
    apply m64Intrinsic_unpaired_side_subset_one_of_two_arcs face F b hsource hcarrier
      hboundary hinter p hp
      (isCompact_Icc.image (m64Intrinsic_contDiff_boundary 1).continuous).isClosed
      (isCompact_Icc.image hb.continuous).isClosed _ v0 v1 hmeetImages
    rw [← htrace]
    exact m64Intrinsic_unpaired_side_subset_region_frontier face F b hsource hboundary hinter p hp
  have hturn := m64Intrinsic_region_circle_geodesic_turning_le N face F b hF hFi hsource
    hboundary hinj hinter Q hab hcircleInj hb hgeo hbi hunit hclass
  linarith

end PoincareConjecture
