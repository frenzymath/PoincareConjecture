import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleRegionCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcBoundaryTurning
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCrossing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_triangle_region_angle_le_original_turning
    (N : IntrinsicAnnulus) {U V : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation (closure U))
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (hci : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hbi : InjOn beta (Icc 0 B))
    (hcreg : ∀ t ∈ Ioo 0 D, deriv base t ≠ 0)
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hreg0 : deriv base 0 ≠ 0) (hreg1 : deriv base D ≠ 0)
    (horth0 : N.metric.inner (base 0) (deriv base 0) (deriv alpha 0) = 0)
    (horth1 : N.metric.inner (base D) (deriv base D) (deriv beta 0) = 0)
    (hageo : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hbgeo : N.metric.IsGeodesicOn beta (Icc 0 B))
    (haunit : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hbunit : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    {a b : ℝ} (habound : a ≤ b)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    (hcircle : base '' Icc 0 D = intrinsicAnnulusBoundary 1 '' Icc a b)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward0 : 0 < inner ℝ (base 0) (deriv alpha 0))
    (hinward1 : 0 < inner ℝ (base D) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (v0 v1 vT : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = base 0) (hv1 : v1.1 = base D) (hvT : vT.1 = alpha A) :
    coordinateVertexAngleContribution N.metric R.coordinates R.basis vT.1 ≤
      (∫ x in closure U, N.connection.scalarCurvature x / 2 ∂N.metric.volumeMeasure) +
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  classical
  let Q (i : Fin R.count) := N.metric.alignedChartFrame
    (coordinateTriangleChart (R.coordinates i) (R.basis i))
    (coordinateTriangleChart_smooth (R.coordinates i) (R.basis i) (R.inverse_smooth i))
    (coordinateTriangleChart_smooth_symm (R.coordinates i) (R.basis i) (R.smooth i))
  have hnorm (t : ℝ) (ht : t ∈ Icc 0 D) : ‖base t‖ = 1 := by
    have hp : base t ∈ intrinsicAnnulusBoundary 1 '' Icc a b := by
      rw [← hcircle]
      exact mem_image_of_mem base ht
    obtain ⟨s, _, hs⟩ := hp
    rw [← hs, m64Intrinsic_inner_boundary_norm]
  have hareg (t : ℝ) (ht : t ∈ Ioo 0 A) : deriv alpha t ≠ 0 := by
    intro hz
    have hu := haunit t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hbreg (t : ℝ) (ht : t ∈ Ioo 0 B) : deriv beta t ≠ 0 := by
    intro hz
    have hu := hbunit t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hangle := m64Intrinsic_triangle_region_angle_le_curvature_turning N R Q hc ha hb
    hD hA hB hci hai hbi hcreg hareg hbreg hstartA hstartB hmeet hbaseA hbaseB hsides
    hreg0 hreg1 horth0 horth1 hU hV hUV hfront hfV hclosure hVconn
    (hnorm 0 ⟨le_rfl, hD.le⟩) (hnorm D ⟨hD.le, le_rfl⟩) hinward0 hinward1 hsub
    v0 v1 vT hv0 hv1 hvT
  let gamma (e : Bool) := if e then beta else base
  let T (e : Bool) := if e then B else D
  have hg (e : Bool) : Continuous (gamma e) := by
    cases e
    · exact hc.continuous
    · exact hb.continuous
  have hba : ∀ s ∈ Icc 0 B, ∀ t ∈ Icc 0 A, beta s = alpha t → s = B ∧ t = A := by
    intro s hs t ht he
    exact (hsides t ht s hs he.symm).symm
  have hfront' : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ alpha '' Icc 0 A := by
    change frontier U = base '' Icc 0 D ∪ beta '' Icc 0 B ∪ alpha '' Icc 0 A
    exact hfront.trans (by ac_rfl)
  let eta (e : Bool) := if e then alpha else beta
  let L (e : Bool) := if e then A else B
  have he (e : Bool) : ContDiff ℝ ∞ (eta e) := by
    cases e
    · exact hb
    · exact ha
  have hegeo (e : Bool) : N.metric.IsGeodesicOn (eta e) (Icc 0 (L e)) := by
    cases e
    · exact hbgeo
    · exact hageo
  have hei (e : Bool) : InjOn (eta e) (Icc 0 (L e)) := by
    cases e
    · exact hbi
    · exact hai
  have heunit (e : Bool) : ∀ t ∈ Icc 0 (L e),
      N.metric.inner (eta e t) (deriv (eta e) t) (deriv (eta e) t) = 1 := by
    cases e
    · exact hbunit
    · exact haunit
  have hclass (p : Fin R.count × Fin 3)
      (hp : ∀ q : Fin R.count × Fin 3,
        faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p) :
      ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
        intrinsicAnnulusBoundary 1 '' Icc a b ∨
      ∃ e, ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ eta e '' Icc 0 (L e) := by
    rcases m64Intrinsic_three_arc_unpaired_side_classification R gamma alpha T hg
        ha.continuous hbaseB hbaseA hba hU hV hUV hfront' hfV
        v0 v1 vT hv0 hv1 (hvT.trans hmeet) p hp with hs | hs | hs
    · exact Or.inl (hs.trans hcircle.subset)
    · exact Or.inr ⟨false, hs⟩
    · exact Or.inr ⟨true, hs⟩
  have hturn := m64Intrinsic_region_circle_two_geodesics_turning_le N R Q
    habound hcircleInj eta L he hegeo hei heunit hclass
  linarith

end PoincareConjecture
