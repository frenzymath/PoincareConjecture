import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AnnularCollisionFocusing
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PrescribedCollisionDisk
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_embedded_normal_collision_cyclic_focusing
    (N : IntrinsicAnnulus) {K delta r q mu curvatureCutoff h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (hcutoff : 100 * delta / q ≤ curvatureCutoff)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
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
    (hmetric : ∀ p, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ curvatureCutoff →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v))
    {a b A B : ℝ} (hab : a < b) (hperiod : b - a < rampPeriod)
    (hAh : A ≤ h) (hBh : B ≤ h) (hAheight : A ≤ height a) (hBheight : B ≤ height b)
    (hai : InjOn (fun t => e !₂[a, t]) (Icc 0 A))
    (hbi : InjOn (fun t => e !₂[b, t]) (Icc 0 B))
    (haInterior : ∀ t ∈ Ioc 0 A, 1 < ‖e !₂[a, t]‖ ∧ ‖e !₂[a, t]‖ ≤ 2)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖e !₂[b, t]‖ ∧ ‖e !₂[b, t]‖ ≤ 2)
    (hmeet : ∃ t ∈ Icc 0 A, ∃ s ∈ Icc 0 B, e !₂[a, t] = e !₂[b, s]) :
    (intrinsicBoundaryLength N.metric 1 a b ≤ 2 * q ∧
      Real.cos (Real.sqrt (max K 1) * (q / 10)) * intrinsicBoundaryLength N.metric 1 a b ≤
      (Real.sin (Real.sqrt (max K 1) * (q / 10)) / Real.sqrt (max K 1)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) ∨
    (intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) ≤ 2 * q ∧
      Real.cos (Real.sqrt (max K 1) * (q / 10)) *
        intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) ≤
      (Real.sin (Real.sqrt (max K 1) * (q / 10)) / Real.sqrt (max K 1)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 b (a + rampPeriod)) := by
  let u : ℝ × ℝ → AnnulusCoordinates := fun z => e !₂[z.1, z.2]
  have hu : ContDiff ℝ ∞ u := he.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_snd)
  have hsmooth (p : ℝ) : ContDiff ℝ ∞ (fun t => e !₂[p, t]) := he.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id)
  have hunit (p : ℝ) : ∀ t ∈ Icc 0 (height p), N.metric.inner (e !₂[p, t])
      (deriv (fun s => e !₂[p, s]) t) (deriv (fun s => e !₂[p, s]) t) = 1 := by
    have hzero : N.metric.inner (e !₂[p, 0])
        (curveVelocity (n := 2) (fun t => e !₂[p, t]) 0)
        (curveVelocity (n := 2) (fun t => e !₂[p, t]) 0) = 1 := by
      rw [m64Intrinsic_curveVelocity_eq_deriv, (hderiv p).deriv, hbase p]
      exact hunit0 p
    have hu := m64Intrinsic_geodesic_velocity_unit N (hAnn p).1 (hgeodesic p) Subset.rfl hzero
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hu
  obtain ⟨s, t, U, V, hs, hsA, ht, htB, hst, hfirst, hU, hV, _, hpV, _, hbV,
      hd, hc, hfV, _, hsub, hfront⟩ :=
    m64Intrinsic_exists_prescribed_collision_disk hu hbase hab hperiod hai hbi
      haInterior hbInterior hmeet
  let gamma₁ : ℝ → AnnulusCoordinates := fun t => e !₂[a, t]
  let gamma₂ : ℝ → AnnulusCoordinates := fun t => e !₂[b, t]
  have hi₁ : InjOn gamma₁ (Icc 0 s) := hai.mono (Icc_subset_Icc_right hsA)
  have hi₂ : InjOn gamma₂ (Icc 0 t) := hbi.mono (Icc_subset_Icc_right htB)
  have hg₁ : N.metric.IsGeodesicOn gamma₁ (Icc 0 s) :=
    fun v hv => hgeodesic a v ⟨hv.1, hv.2.trans (hsA.trans hAheight)⟩
  have hg₂ : N.metric.IsGeodesicOn gamma₂ (Icc 0 t) :=
    fun v hv => hgeodesic b v ⟨hv.1, hv.2.trans (htB.trans hBheight)⟩
  have hu₁ : ∀ v ∈ Icc 0 s, N.metric.inner (gamma₁ v) (deriv gamma₁ v) (deriv gamma₁ v) = 1 :=
    fun v hv => hunit a v ⟨hv.1, hv.2.trans (hsA.trans hAheight)⟩
  have hu₂ : ∀ v ∈ Icc 0 t, N.metric.inner (gamma₂ v) (deriv gamma₂ v) (deriv gamma₂ v) = 1 :=
    fun v hv => hunit b v ⟨hv.1, hv.2.trans (htB.trans hBheight)⟩
  have ho₁ : N.metric.inner (intrinsicAnnulusBoundary 1 a)
      (deriv (intrinsicAnnulusBoundary 1) a) (deriv gamma₁ 0) = 0 := by
    rw [(hderiv a).deriv]
    exact horth0 a
  have ho₂ : N.metric.inner (intrinsicAnnulusBoundary 1 b)
      (deriv (intrinsicAnnulusBoundary 1) b) (deriv gamma₂ 0) = 0 := by
    rw [(hderiv b).deriv]
    exact horth0 b
  have hn₁ : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (deriv gamma₁ 0) := by
    rw [(hderiv a).deriv]
    exact hinward0 a
  have hn₂ : 0 < inner ℝ (intrinsicAnnulusBoundary 1 b) (deriv gamma₂ 0) := by
    rw [(hderiv b).deriv]
    exact hinward0 b
  rcases hfront with hfront | hfront
  · exact Or.inl (m64Intrinsic_normal_collision_annular_focusing N (hsmooth a) (hsmooth b)
      hab hs ht hi₁ hi₂ (hbase a) (hbase b) hst hfirst ho₁ ho₂ hg₁ hg₂ hu₁ hu₂
      (fun v hv => (haInterior v ⟨hv.1, hv.2.trans hsA⟩).1)
      (fun v hv => (hbInterior v ⟨hv.1, hv.2.trans htB⟩).1) hn₁ hn₂
      hperiod hq hqr (hsA.trans hAh) (htB.trans hBh) hhq
      hU hV hpV.isConnected.isPreconnected hbV hd hc hfV hfront hsub
      hK hdelta hdeltaSmall hturn harea hbudget hmodel hcutoff hareaLoss
      e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric)
  · have hshift : gamma₁ 0 = intrinsicAnnulusBoundary 1 (a + rampPeriod) := by
      simpa only [m64Intrinsic_boundary_periodic 1 a] using hbase a
    have hdshift : deriv (intrinsicAnnulusBoundary 1) (a + rampPeriod) =
        deriv (intrinsicAnnulusBoundary 1) a := by
      have hs : (fun p => intrinsicAnnulusBoundary 1 (p + rampPeriod)) =
          intrinsicAnnulusBoundary 1 := funext (m64Intrinsic_boundary_periodic 1)
      rw [← deriv_comp_add_const, hs]
    have hoshift : N.metric.inner (intrinsicAnnulusBoundary 1 (a + rampPeriod))
        (deriv (intrinsicAnnulusBoundary 1) (a + rampPeriod)) (deriv gamma₁ 0) = 0 := by
      change N.metric.euclideanCoefficients (intrinsicAnnulusBoundary 1 (a + rampPeriod))
        (deriv (intrinsicAnnulusBoundary 1) (a + rampPeriod)) (deriv gamma₁ 0) = 0
      rw [m64Intrinsic_boundary_periodic 1 a, hdshift]
      exact ho₁
    have hnshift : 0 < inner ℝ (intrinsicAnnulusBoundary 1 (a + rampPeriod)) (deriv gamma₁ 0) := by
      simpa only [m64Intrinsic_boundary_periodic 1 a] using hn₁
    have hfirst' : ∀ x ∈ Icc 0 t, ∀ y ∈ Icc 0 s,
        gamma₂ x = gamma₁ y → x = t ∧ y = s := by
      intro x hx y hy heq
      exact (hfirst y hy x hx heq.symm).symm
    exact Or.inr (m64Intrinsic_normal_collision_annular_focusing N (hsmooth b) (hsmooth a)
      (by linarith only [hperiod]) ht hs hi₂ hi₁ (hbase b) hshift hst.symm hfirst'
      ho₂ hoshift hg₂ hg₁ hu₂ hu₁
      (fun v hv => (hbInterior v ⟨hv.1, hv.2.trans htB⟩).1)
      (fun v hv => (haInterior v ⟨hv.1, hv.2.trans hsA⟩).1) hn₂ hnshift
      (by linarith only [hab]) hq hqr (htB.trans hBh) (hsA.trans hAh) hhq
      hU hV hpV.isConnected.isPreconnected hbV hd hc hfV hfront hsub
      hK hdelta hdeltaSmall hturn harea hbudget hmodel hcutoff hareaLoss
      e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric)

end PoincareConjecture
