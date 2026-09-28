import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConstructedThreeArcCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionCurvature





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture





theorem m64Intrinsic_constructed_no_short_three_arc_region
    (N : IntrinsicAnnulus)
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
    (hregular : ∀ t ∈ Ioo 0 (T false), deriv (gamma false) t ≠ 0)
    (hreg0 : deriv (gamma false) 0 ≠ 0)
    (horth : N.metric.inner (gamma false 0) (deriv (gamma false) 0) (deriv sigma 0) = 0)
    (hgeo : N.metric.IsGeodesicOn (gamma true) (Icc 0 (T true)))
    (hsgeo : N.metric.IsGeodesicOn sigma (Icc 0 S))
    (hunit : ∀ t ∈ Icc 0 (T true),
      N.metric.inner (gamma true t) (deriv (gamma true) t) (deriv (gamma true) t) = 1)
    (hsunit : ∀ t ∈ Icc 0 S, N.metric.inner (sigma t) (deriv sigma t) (deriv sigma t) = 1)
    (hind1 : LinearIndependent ℝ
      (![-deriv (gamma true) (T true), -deriv sigma S] : Fin 2 → AnnulusCoordinates))
    {a b : ℝ} (habound : a ≤ b)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    (hcircle : gamma false '' Icc 0 (T false) = intrinsicAnnulusBoundary 1 '' Icc a b)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward : 0 < inner ℝ (gamma false 0) (deriv sigma 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta r mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hperiod : b ≤ a + rampPeriod)
    (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ r) : False := by
  have hcompact : IsCompact (closure U) :=
    m64Intrinsic_standardAnnulus_isCompact.of_isClosed_subset isClosed_closure hsub
  have hlower := m64Intrinsic_constructed_three_arc_region_curvature_lower_bound N
    gamma sigma T hg hs hT hS hspeed hinj hsi hstart hend hjoin hreg htan hab has hbs
    hregular hreg0 horth hgeo hsgeo hunit hsunit hind1 habound hcircleInj hcircle
    hU hV hUV hfront hfV hclosure hVconn hinward hsub
  have hupper := m64Intrinsic_region_gaussian_integral_le_area N hK hcompact hsub
  have hscaled : max K 0 * intrinsicAnnulusArea N.metric ≤ max K 0 * mu :=
    mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
  have hlocalTurn := hturn a b habound hperiod hshort
  linarith only [hlower, hupper, hscaled, hbudget, hlocalTurn]

end PoincareConjecture
