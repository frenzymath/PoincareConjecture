import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcRegionCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcBoundaryTurning
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCrossing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_three_arc_region_curvature_lower_bound
    (N : IntrinsicAnnulus) {U V : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation (closure U))
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hregular : ∀ t ∈ Ioo (0 : ℝ) (T false), deriv (gamma false) t ≠ 0)
    (hreg0 : deriv (gamma false) 0 ≠ 0)
    (horth : N.metric.inner (gamma false 0) (deriv (gamma false) 0) (deriv sigma 0) = 0)
    (hgeo : N.metric.IsGeodesicOn (gamma true) (Icc 0 (T true)))
    (hsgeo : N.metric.IsGeodesicOn sigma (Icc 0 S))
    (hunit : ∀ t ∈ Icc 0 (T true),
      N.metric.inner (gamma true t) (deriv (gamma true) t) (deriv (gamma true) t) = 1)
    (hsunit : ∀ t ∈ Icc 0 S, N.metric.inner (sigma t) (deriv sigma t) (deriv sigma t) = 1)
    {a b : ℝ} (habound : a ≤ b)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    (hcircle : gamma false '' Icc 0 (T false) = intrinsicAnnulusBoundary 1 '' Icc a b)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfU : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward : 0 < inner ℝ (gamma false 0) (deriv sigma 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (v0 vj v1 : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = gamma false 0) (hvj : vj.1 = gamma false (T false))
    (hv1 : v1.1 = gamma true (T true)) :
    Real.pi / 2 - intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b ≤
      ∫ x in closure U, N.connection.scalarCurvature x / 2 ∂N.metric.volumeMeasure := by
  classical
  let Q (i : Fin R.count) := N.metric.alignedChartFrame
    (coordinateTriangleChart (R.coordinates i) (R.basis i))
    (coordinateTriangleChart_smooth (R.coordinates i) (R.basis i) (R.inverse_smooth i))
    (coordinateTriangleChart_smooth_symm (R.coordinates i) (R.basis i) (R.smooth i))
  have hnorm : ‖gamma false 0‖ = 1 := by
    have hp : gamma false 0 ∈ intrinsicAnnulusBoundary 1 '' Icc a b := by
      rw [← hcircle]
      exact ⟨0, ⟨le_rfl, (hT false).le⟩, rfl⟩
    obtain ⟨t, _, ht⟩ := hp
    rw [← ht, m64Intrinsic_inner_boundary_norm]
  have hg1reg (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (T true)) : deriv (gamma true) t ≠ 0 := by
    intro hz
    have hu := hunit t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hsreg (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) : deriv sigma t ≠ 0 := by
    intro hz
    have hu := hsunit t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hgreg (e : Bool) : ∀ t ∈ Ioo (0 : ℝ) (T e), deriv (gamma e) t ≠ 0 := by
    cases e
    · exact hregular
    · exact hg1reg
  have hcurvature := m64Intrinsic_three_arc_region_curvature_turning_ge_pi_div_two
    N R Q gamma sigma T hg hs hT hS hspeed hinj hsi hstart hend hjoin hreg htan
    hab has hbs hgreg hsreg hreg0 horth hU hV hUV hfU hfV hclosure hVconn
    hnorm hinward hsub v0 v1 hv0 hv1
  let eta (e : Bool) := if e then sigma else gamma true
  let L (e : Bool) := if e then S else T true
  have he (e : Bool) : ContDiff ℝ ∞ (eta e) := by
    cases e
    · exact hg true
    · exact hs
  have hegeo (e : Bool) : N.metric.IsGeodesicOn (eta e) (Icc 0 (L e)) := by
    cases e
    · exact hgeo
    · exact hsgeo
  have hei (e : Bool) : InjOn (eta e) (Icc 0 (L e)) := by
    cases e
    · exact hinj true
    · exact hsi
  have heunit (e : Bool) : ∀ t ∈ Icc 0 (L e),
      N.metric.inner (eta e t) (deriv (eta e) t) (deriv (eta e) t) = 1 := by
    cases e
    · exact hunit
    · exact hsunit
  have hclass (p : Fin R.count × Fin 3)
      (hp : ∀ q : Fin R.count × Fin 3,
        faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p) :
      ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
        intrinsicAnnulusBoundary 1 '' Icc a b ∨
      ∃ e, ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ eta e '' Icc 0 (L e) := by
    rcases m64Intrinsic_three_arc_unpaired_side_classification R gamma sigma T
        (fun e => (hg e).continuous) hs.continuous hab has hbs hU hV hUV hfU hfV
        v0 vj v1 hv0 hvj hv1 p hp with hc | hc | hc
    · exact Or.inl (hc.trans hcircle.subset)
    · exact Or.inr ⟨false, hc⟩
    · exact Or.inr ⟨true, hc⟩
  have hturn := m64Intrinsic_region_circle_two_geodesics_turning_le N R Q
    habound hcircleInj eta L he hegeo hei heunit hclass
  linarith

end PoincareConjecture
