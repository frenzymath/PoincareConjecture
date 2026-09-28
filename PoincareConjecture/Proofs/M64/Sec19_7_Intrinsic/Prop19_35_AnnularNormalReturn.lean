import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalNormalReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AnnularBigonRegion
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_no_annular_normal_return
    (N : IntrinsicAnnulus) {K delta r q mu alpha h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hh : 0 < h) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / q ≤ alpha)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b T : ℝ} (hab : a < b) (hperiod : b - a < rampPeriod)
    (hT : 0 < T) (hTh : T ≤ h) (hgi : InjOn gamma (Icc 0 T))
    (h0 : gamma 0 = intrinsicAnnulusBoundary 1 a)
    (h1 : gamma T = intrinsicAnnulusBoundary 1 b)
    (hinside : ∀ t ∈ Ioo 0 T, 1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2)
    (hgeo : N.metric.IsGeodesicOn gamma (Icc 0 T))
    (hunit : N.metric.inner (gamma 0) (deriv gamma 0) (deriv gamma 0) = 1)
    (horth : N.metric.inner (intrinsicAnnulusBoundary 1 a)
      (deriv (intrinsicAnnulusBoundary 1) a) (deriv gamma 0) = 0)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (deriv gamma 0))
    (hterminal : LinearIndependent ℝ
      (![deriv (intrinsicAnnulusBoundary 1) b, deriv gamma T] : Fin 2 → AnnulusCoordinates))
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates) (height : ℝ → ℝ)
    (hbase : ∀ p, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hunit0 : ∀ p, N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    (horth0 : ∀ p, N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0)
    (hinward0 : ∀ p, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hAnn : ∀ p, 0 < height p ∧
      (height p = h ∨ ‖e !₂[p, height p]‖ = 1 ∨ ‖e !₂[p, height p]‖ = 2))
    (hgeodesic : ∀ p, N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (height p)))
    (hmetric : ∀ p, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) : False := by
  obtain ⟨U, V, hU, hV, _, hpV, _, hbV, hUV, hcover, hfV, _, hsub, hfront⟩ :=
    m64Intrinsic_embedded_inner_return_annular_region hab hperiod hT hg.continuous
      hgi h0 h1 hinside
  rcases hfront with hfront | hfront
  · have hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc (min a b) (max a b) ∪
        gamma '' Icc 0 T := by simpa only [min_eq_left hab.le, max_eq_right hab.le] using hfront
    exact m64Intrinsic_no_regional_normal_return N hK hdelta hdeltaSmall hq hqr hh hhq
      hturn halpha harea hbudget hmodel hareaLoss hg hT hTh hgi h0 h1
      (fun t ht => (hinside t ht).1) hgeo hunit horth hinward hterminal
      (by simpa only [abs_of_pos (sub_pos.mpr hab)] using hperiod)
      hU hV hpV.isConnected.isPreconnected hbV hUV hcover hfV.symm hsub hfU
      e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric
  · have hba : b < a + rampPeriod := by linarith only [hperiod]
    have hfU : frontier U =
        intrinsicAnnulusBoundary 1 '' Icc (min (a + rampPeriod) b) (max (a + rampPeriod) b) ∪
          gamma '' Icc 0 T := by
      simpa only [min_eq_right hba.le, max_eq_left hba.le] using hfront
    have hdshift : deriv (intrinsicAnnulusBoundary 1) (a + rampPeriod) =
        deriv (intrinsicAnnulusBoundary 1) a := by
      have hs : (fun p => intrinsicAnnulusBoundary 1 (p + rampPeriod)) =
          intrinsicAnnulusBoundary 1 := funext (m64Intrinsic_boundary_periodic 1)
      rw [← deriv_comp_add_const, hs]
    exact m64Intrinsic_no_regional_normal_return N hK hdelta hdeltaSmall hq hqr hh hhq
      hturn halpha harea hbudget hmodel hareaLoss hg hT hTh hgi
      (by simpa only [m64Intrinsic_boundary_periodic 1 a] using h0) h1
      (fun t ht => (hinside t ht).1) hgeo hunit
      (by
        change N.metric.euclideanCoefficients (intrinsicAnnulusBoundary 1 (a + rampPeriod))
          (deriv (intrinsicAnnulusBoundary 1) (a + rampPeriod)) (deriv gamma 0) = 0
        rw [m64Intrinsic_boundary_periodic 1 a, hdshift]
        exact horth)
      (by simpa only [m64Intrinsic_boundary_periodic 1 a] using hinward) hterminal
      (by rw [abs_of_neg (sub_neg.mpr hba)]; linarith only [hab])
      hU hV hpV.isConnected.isPreconnected hbV hUV hcover hfV.symm hsub hfU
      e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric

end PoincareConjecture
