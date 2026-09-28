import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalArcRetainedDomain
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalArcRetainedBaseLength
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InjectiveStripArea

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

theorem m64Intrinsic_exists_local_arc_retained_strip
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : Differentiable ℝ e) {height : ℝ → ℝ} (hh : Measurable height)
    {l u delta r alpha R rho kappa : ℝ}
    (hlu : l < u) (hperiod : u ≤ l + rampPeriod)
    (hlength : intrinsicBoundaryLength N.metric 1 l u = r)
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100) (hr : 0 < r)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / r ≤ alpha)
    (hR : 0 < R) (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hangle : kappa * rho ≤ Real.pi / 4) (hrhoSmall : rho ≤ r / (400 * delta))
    (harea : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * R * (r / 10))
    (hheight : ∀ a ∈ Ioo l u,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha → 0 ≤ height a)
    (hray : ∀ a ∈ Ioo l u,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)))
    (hfocus : ∀ a ∈ Ioo l u,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      ∀ b ∈ Ioo l u,
        intrinsicGeodesicCurvature N.metric N.connection 1 b ≤ alpha → a < b →
        (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b), e !₂[a, t] = e !₂[b, s]) →
        Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b)
    (hmetric : ∀ x : AnnulusCoordinates, x 0 ∈ Ioo l u →
      intrinsicGeodesicCurvature N.metric N.connection 1 (x 0) ≤ alpha →
      x 1 ∈ Icc 0 (height (x 0)) → ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v))
    (himage : ∀ x : AnnulusCoordinates, x 0 ∈ Ioo l u →
      intrinsicGeodesicCurvature N.metric N.connection 1 (x 0) ≤ alpha →
      x 1 ∈ Icc 0 (height (x 0)) → e x ∈ standardAnnulusDomain) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc l u ∧
      (∫ s in E, intrinsicBoundarySpeed N.metric 1 s) < r / 50 ∧
      let S := (Ioo l u ∩
        {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}) \ E
      let Z := S ∩ {s | height s < R}
      MeasurableSet S ∧ MeasurableSet Z ∧
      InjOn e {z : AnnulusCoordinates | z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))} ∧
      InjOn (fun a => e !₂[a, height a]) Z ∧
      m64IntrinsicLocalHighCurvatureLength N alpha l u < r / 100 ∧
      m64IntrinsicLongFiberLength N S height R < r / 10 ∧
      87 * r / 100 < ∫ s in Z, intrinsicBoundarySpeed N.metric 1 s := by
  let X := Ioo l u ∩
    {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}
  have hX : X ⊆ Ioo l u := inter_subset_left
  have hXm : MeasurableSet X := measurableSet_Ioo.inter (measurableSet_le
    (m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0)).measurable
    measurable_const)
  obtain ⟨E, hE, hEsub, hfocusBound, hinj⟩ :=
    m64Intrinsic_exists_local_arc_retained_domain_with_sine_focusing N e height hlu hX
      hrho hkappa hangle (fun a ha => hray a ha.1 ha.2)
      (fun a ha b hb hab hmeet => hfocus a ha.1 ha.2 b hb.1 hb.2 hab hmeet)
  have hturnLocal : intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 l u < delta :=
    hturn l u hlu.le hperiod hlength.le
  have hfocusLoss : (∫ s in E, intrinsicBoundarySpeed N.metric 1 s) < r / 50 := by
    have hstrict := hfocusBound.trans_lt (mul_lt_mul_of_pos_left hturnLocal
      (by positivity : 0 < 8 * rho))
    have hscale := (le_div_iff₀ (by positivity : 0 < 400 * delta)).mp hrhoSmall
    apply hstrict.trans_le
    nlinarith only [hscale]
  let S := X \ E
  let Z := S ∩ {s | height s < R}
  have hS : MeasurableSet S := hXm.diff hE
  have hZ : MeasurableSet Z := hS.inter (measurableSet_lt hh measurable_const)
  have hSsub : S ⊆ Icc l u := sdiff_subset.trans (hX.trans Ioo_subset_Icc_self)
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
  have hlong := m64Intrinsic_local_long_fiber_length_lt_tenth N hS hSsub hh hc hR hr
    hweighted harea
  have hhigh := m64Intrinsic_local_high_curvature_length_lt_hundredth N
    hdelta hr hlu.le hlength hperiod hturn halpha
  have hendInj : InjOn (fun a => e !₂[a, height a]) Z := by
    intro a ha b hb hab
    have hpair : !₂[a, height a] = !₂[b, height b] := by
      apply hinj
      · exact ⟨ha.1, ⟨hheight a ha.1.1.1 ha.1.1.2, le_rfl⟩⟩
      · exact ⟨hb.1, ⟨hheight b hb.1.1.1 hb.1.1.2, le_rfl⟩⟩
      · exact hab
    have hcoord := congrArg (fun z : AnnulusCoordinates => z 0) hpair
    simpa only [Matrix.cons_val_zero] using hcoord
  refine ⟨E, hE, hEsub, hfocusLoss, hS, hZ, hinj, hendInj, hhigh, hlong, ?_⟩
  have hremaining := m64Intrinsic_local_retained_short_base_length_lower N hlu.le hE hEsub hh
    (alpha := alpha) (R := R)
  dsimp only at hremaining
  change intrinsicBoundaryLength N.metric 1 l u -
      m64IntrinsicLocalHighCurvatureLength N alpha l u -
      (∫ s in E, intrinsicBoundarySpeed N.metric 1 s) -
      m64IntrinsicLongFiberLength N S height R ≤
    ∫ s in Z, intrinsicBoundarySpeed N.metric 1 s at hremaining
  rw [hlength] at hremaining
  change 87 * r / 100 < ∫ s in Z, intrinsicBoundarySpeed N.metric 1 s
  linarith

end PoincareConjecture
