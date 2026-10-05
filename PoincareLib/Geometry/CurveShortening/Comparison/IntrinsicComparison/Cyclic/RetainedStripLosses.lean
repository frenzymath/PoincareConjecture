import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Cyclic.RetainedNormalDomain
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Retained.BaseLength
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Injective.StripArea

/-!
# Three losses for a cyclic retained normal strip

A collision may focus either boundary arc between its base points. The
cyclic focusing removal constructs the injective retained domain, and the
actual strip area estimate bounds its long fibers. The resulting three
losses and short-base length bound follow Morgan--Tian Claim 19.57,
pp. 479-480, and the conclusion of Proposition 19.35, pp. 480-481. The
cyclic repair is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-cyclic-focusing.md`.
Ray injectivity, cyclic focusing, the normal metric bound, and image
containment remain explicit geometric inputs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareMT

/-- Cyclic collision focusing and the actual normal metric bound give the
three exceptional losses of Claim 19.57, pp. 479-480, and Proposition 19.35,
pp. 480-481. Either boundary arc may satisfy the focusing inequality; no
exceptional-set measure or global normal-map injectivity is assumed.
See the project cyclic-focusing derivation dated 2026-09-25. -/
theorem m64Intrinsic_exists_cyclic_retained_strip_three_losses
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : Differentiable ℝ e) {height : ℝ → ℝ} (hh : Measurable height)
    {delta r alpha R rho kappa : ℝ}
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / r ≤ alpha)
    (hR : 0 < R) (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hangle : kappa * rho ≤ Real.pi / 4)
    (hrhoSmall : rho ≤ 3 * r / (1600 * delta))
    (harea : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * R * (r / 10))
    (hray : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)))
    (hfocus : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      ∀ b ∈ Ico (0 : ℝ) rampPeriod,
        intrinsicGeodesicCurvature N.metric N.connection 1 b ≤ alpha → a < b →
        (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b), e !₂[a, t] = e !₂[b, s]) →
        (Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) ∨
        (Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 b (a + rampPeriod)))
    (hmetric : ∀ x : AnnulusCoordinates, x 0 ∈ Ico (0 : ℝ) rampPeriod →
      intrinsicGeodesicCurvature N.metric N.connection 1 (x 0) ≤ alpha →
      x 1 ∈ Icc 0 (height (x 0)) → ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v))
    (himage : ∀ x : AnnulusCoordinates, x 0 ∈ Ico (0 : ℝ) rampPeriod →
      intrinsicGeodesicCurvature N.metric N.connection 1 (x 0) ≤ alpha →
      x 1 ∈ Icc 0 (height (x 0)) → e x ∈ standardAnnulusDomain) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) rampPeriod ∧
      (∫ s in E, intrinsicBoundarySpeed N.metric 1 s) <
        3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 ∧
      let S := (Ico (0 : ℝ) rampPeriod ∩
        {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}) \ E
      let Z := S ∩ {s | height s < R}
      MeasurableSet S ∧ MeasurableSet Z ∧
      InjOn e {z : AnnulusCoordinates | z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))} ∧
      m64IntrinsicHighCurvatureLength N alpha <
        intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 ∧
      m64IntrinsicLongFiberLength N S height R <
        intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10 ∧
      (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod <
        (1 - delta) * ∫ s in Z, intrinsicBoundarySpeed N.metric 1 s := by
  let X := Ico (0 : ℝ) rampPeriod ∩
    {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}
  have hX : X ⊆ Ico (0 : ℝ) rampPeriod := inter_subset_left
  have hXm : MeasurableSet X := measurableSet_Ico.inter (measurableSet_le
    (m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0)).measurable
    measurable_const)
  obtain ⟨E, hE, hEsub, hfocusLoss, hinj⟩ :=
    m64Intrinsic_exists_cyclic_retained_domain_with_focusing_loss N e height hX
      hdelta hr hfirst hturn hrho hkappa hangle hrhoSmall
      (fun a ha => hray a ha.1 ha.2)
      (fun a ha b hb hab hmeet => hfocus a ha.1 ha.2 b hb.1 hb.2 hab hmeet)
  let S := X \ E
  have hS : MeasurableSet S := hXm.diff hE
  have hSsub : S ⊆ Icc (0 : ℝ) rampPeriod :=
    sdiff_subset.trans (hX.trans Ico_subset_Icc_self)
  have hweighted : ENNReal.ofReal ((1 - delta) ^ 2) *
      (∫⁻ s in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 s) *
        ENNReal.ofReal (height s)) ≤ ENNReal.ofReal (intrinsicAnnulusArea N.metric) := by
    apply m64Intrinsic_injective_strip_height_integral_le N.metric he hS hh
      (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous.measurable
      hinj
    · intro x hx ht v
      exact hmetric x hx.1.1 hx.1.2 ht v
    · rintro _ ⟨x, hx, rfl⟩
      exact himage x hx.1.1.1 hx.1.1.2 hx.2
  have hc : 0 < 1 - delta := by linarith
  have hlong := m64Intrinsic_long_fiber_length_lt_tenth N hS hSsub hh hc hR
    hfirst hweighted harea
  refine ⟨E, hE, hEsub, hfocusLoss, hS,
    hS.inter (measurableSet_lt hh measurable_const), hinj,
    m64Intrinsic_high_curvature_length_lt N hdelta hr hfirst hturn halpha, hlong, ?_⟩
  exact m64Intrinsic_retained_short_base_stretched_length_gt N hdelta hdeltaSmall hr
    hfirst hturn halpha hE hEsub hh hfocusLoss hlong

end PoincareMT
