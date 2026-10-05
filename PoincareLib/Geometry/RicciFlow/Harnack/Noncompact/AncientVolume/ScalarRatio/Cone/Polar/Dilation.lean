import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Transitions
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareLib.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareLib.Geometry.Riemannian.Curvature.Bounds.Operator

/-!
# Dilation of actual radial cone models

Positive radial dilation is a homeomorphism of the constructed metric cone.
Composing a retained radial chart with it scales its metric and potential
by the square of the radius. Flatness, the Hessian identity, and the eikonal
identity are derived for the scaled data. No smooth cone structure is used.

Reference: Kleiner--Lott (corrected 2013), Theorem 41.2, Case 2, p. 2677.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set TopologicalSpace PoincareMT
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Scaling both the metric and the scalar by the same constant preserves
the actual gradient vector. -/
theorem rescaledMetric_gradient_const_mul (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) (f : M → ℝ) (x : M) :
    (rescaledMetric_connection g D c hc).gradient (fun y => c * f y) x =
      D.gradient f x := by
  apply ((rescaledMetric g c hc).inner_isInvertible x).injective
  ext v
  rw [(rescaledMetric_connection g D c hc).inner_gradient, mvfderiv_const_mul,
    rescaledMetric_inner, D.inner_gradient]

/-- The retained connection and hence the Hessian are unchanged by constant
metric scaling. -/
theorem rescaledMetric_hessian (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) (f : M → ℝ) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (rescaledMetric_connection g D c hc).hessian f x v w = D.hessian f x v w := rfl

end PoincareMT

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} (hcomparison : RayComparison p)

/-- Positive dilation of the actual metric cone, with reciprocal dilation
as its inverse. -/
def asymptoticConeDilationHomeomorph (c : ℝ≥0) (hc : 0 < c) :
    AsymptoticCone p hcomparison ≃ₜ AsymptoticCone p hcomparison where
  toFun := asymptoticConeDilation hcomparison c
  invFun := asymptoticConeDilation hcomparison c⁻¹
  left_inv a := by rw [asymptoticConeDilation_mul, inv_mul_cancel₀ hc.ne', asymptoticConeDilation_one]
  right_inv a := by rw [asymptoticConeDilation_mul, mul_inv_cancel₀ hc.ne', asymptoticConeDilation_one]
  continuous_toFun := (continuous_asymptoticConeDilation hcomparison).comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := (continuous_asymptoticConeDilation hcomparison).comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem asymptoticConeDilationHomeomorph_apply (c : ℝ≥0) (hc : 0 < c)
    (a : AsymptoticCone p hcomparison) :
    asymptoticConeDilationHomeomorph hcomparison c hc a =
      asymptoticConeDilation hcomparison c a := rfl

namespace UnitSliceRadialChartData

variable {hcomparison} {n : ℕ}

/-- An actual radial model dilates to another actual radial model. Its
domain is retained, while the ambient metric and potential acquire `c²`. -/
def dilate (d : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c) :
    UnitSliceRadialChartData hcomparison n where
  metric := rescaledMetric d.metric ((c : ℝ) ^ 2) (by positivity)
  connection := rescaledMetric_connection d.metric d.connection ((c : ℝ) ^ 2) (by positivity)
  potential := fun x => (c : ℝ) ^ 2 * d.potential x
  smooth := contMDiff_const.mul d.smooth
  ambientChart := d.ambientChart.transHomeomorph (asymptoticConeDilationHomeomorph hcomparison c hc)
  positive x hx := mul_pos (by positivity) (d.positive x hx)
  hessian x hx v w := by
    rw [rescaledMetric_hessian, d.connection.hessian_const_mul, d.hessian x hx,
      rescaledMetric_inner]
  eikonal x hx := by
    simp only [LeviCivitaData.levelQ, rescaledMetric_gradient_const_mul, rescaledMetric_inner]
    change (c : ℝ) ^ 2 * d.connection.levelQ d.potential x = _
    rw [d.eikonal x hx]
    ring
  flat x hx := by
    have hzero (u v w z : UnitSliceAmbient n) : d.connection.curvatureTensor x u v w z = 0 := by
      have h := d.connection.abs_curvatureTensor_le_tangentNorm x u v w z
      rw [d.flat x hx] at h
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [zero_mul] using h) (abs_nonneg _)
    simp only [LeviCivitaData.curvatureTensorNorm, rescaledMetric_curvatureTensor, hzero,
      mul_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, Real.sqrt_zero]
  radial x hx := by
    change (asymptoticConeRadius hcomparison
      (asymptoticConeDilation hcomparison c (d.ambientChart x)) : ℝ) ^ 2 / 2 = _
    rw [asymptoticConeRadius_dilation, NNReal.coe_mul, mul_pow, ← d.radial x hx]
    ring
  distance x hx y hy := by
    change dist (asymptoticConeDilation hcomparison c (d.ambientChart x))
      (asymptoticConeDilation hcomparison c (d.ambientChart y)) = _
    rw [dist_asymptoticConeDilation, d.distance x hx y hy, rescaledMetric_edist,
      Real.sqrt_sq c.coe_nonneg, ENNReal.toReal_mul, ENNReal.toReal_ofReal c.coe_nonneg]

@[simp] theorem dilate_source (d : UnitSliceRadialChartData hcomparison n)
    (c : ℝ≥0) (hc : 0 < c) : (d.dilate c hc).ambientChart.source = d.ambientChart.source := rfl

theorem dilate_apply (d : UnitSliceRadialChartData hcomparison n)
    (c : ℝ≥0) (hc : 0 < c) (x : UnitSliceAmbient n) :
    (d.dilate c hc).ambientChart x = asymptoticConeDilation hcomparison c (d.ambientChart x) := rfl

theorem dilate_target (d : UnitSliceRadialChartData hcomparison n)
    (c : ℝ≥0) (hc : 0 < c) :
    (d.dilate c hc).ambientChart.target =
      asymptoticConeDilation hcomparison c '' d.ambientChart.target := by
  ext a
  change asymptoticConeDilation hcomparison c⁻¹ a ∈ d.ambientChart.target ↔ _
  constructor
  · intro ha
    refine ⟨asymptoticConeDilation hcomparison c⁻¹ a, ha, ?_⟩
    rw [asymptoticConeDilation_mul, mul_inv_cancel₀ hc.ne', asymptoticConeDilation_one]
  · rintro ⟨a, ha, rfl⟩
    simpa only [asymptoticConeDilation_mul, inv_mul_cancel₀ hc.ne',
      asymptoticConeDilation_one] using ha

theorem dilate_inner (d : UnitSliceRadialChartData hcomparison n)
    (c : ℝ≥0) (hc : 0 < c) (x v w : UnitSliceAmbient n) :
    (d.dilate c hc).metric.inner x v w = (c : ℝ) ^ 2 * d.metric.inner x v w := rfl

theorem dilate_gradient (d : UnitSliceRadialChartData hcomparison n)
    (c : ℝ≥0) (hc : 0 < c) (x : UnitSliceAmbient n) :
    (d.dilate c hc).connection.gradient (d.dilate c hc).potential x =
      d.connection.gradient d.potential x :=
  rescaledMetric_gradient_const_mul d.metric d.connection _ _ d.potential x

/-- Overlaps of dilated models are smooth and preserve the scaled tensors;
this is the coordinate identity used when gluing a polar metric. -/
theorem smooth_isometric_dilate_transition
    (d e : UnitSliceRadialChartData hcomparison n)
    (c b : ℝ≥0) (hc : 0 < c) (hb : 0 < b) :
    let T := (d.dilate c hc).ambientChart.trans (e.dilate b hb).ambientChart.symm
    ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ T T.source ∧
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ T.symm T.target ∧
      ∀ x ∈ T.source, ∀ v w : UnitSliceAmbient n,
        (b : ℝ) ^ 2 * e.metric.inner (T x)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x v)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x w) =
            (c : ℝ) ^ 2 * d.metric.inner x v w := by
  exact (d.dilate c hc).metric.smooth_isometric_charts_of_edist_eq (e.dilate b hb).metric _
    ((d.dilate c hc).metric.edist_eq_on_isometric_chart_transition (e.dilate b hb).metric
      (d.dilate c hc).ambientChart (e.dilate b hb).ambientChart
      (d.dilate c hc).distance (e.dilate b hb).distance)

/-- In original ambient coordinates, cone dilation is a smooth homothety
with the exact squared scale on tangent inner products. -/
theorem smooth_homothety_in_radial_charts
    (d e : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c) :
    let T := (d.dilate c hc).ambientChart.trans e.ambientChart.symm
    ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ T T.source ∧
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ T.symm T.target ∧
      ∀ x ∈ T.source, ∀ v w : UnitSliceAmbient n,
        e.metric.inner (T x)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x v)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x w) =
            (c : ℝ) ^ 2 * d.metric.inner x v w := by
  exact (d.dilate c hc).metric.smooth_isometric_charts_of_edist_eq e.metric _
    ((d.dilate c hc).metric.edist_eq_on_isometric_chart_transition e.metric
      (d.dilate c hc).ambientChart e.ambientChart (d.dilate c hc).distance e.distance)

theorem potential_homothety_in_radial_charts
    (d e : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c)
    {x : UnitSliceAmbient n}
    (hx : x ∈ ((d.dilate c hc).ambientChart.trans e.ambientChart.symm).source) :
    e.potential (((d.dilate c hc).ambientChart.trans e.ambientChart.symm) x) =
      (c : ℝ) ^ 2 * d.potential x := by
  have htarget : (d.dilate c hc).ambientChart x ∈ e.ambientChart.target := hx.2
  change e.potential (e.ambientChart.symm ((d.dilate c hc).ambientChart x)) = _
  rw [← e.radial _ (e.ambientChart.map_target htarget), e.ambientChart.right_inv htarget]
  exact (d.dilate c hc).radial x hx.1

end UnitSliceRadialChartData

/-- Covering the unit slice by the constructed radial models covers every
positive-radius cone point by an actual dilated model. -/
theorem exists_dilated_radial_model_at_positive_point {n : ℕ}
    (hcover : ∀ z : AsymptoticConeUnitSlice p hcomparison,
      ∃ (d : UnitSliceRadialChartData hcomparison n) (x : d.Level),
        (d.levelHomeomorph x).1 = z)
    (a : AsymptoticConePositive p hcomparison) :
    ∃ (d : UnitSliceRadialChartData hcomparison n) (x : UnitSliceAmbient n),
      x ∈ d.ambientChart.source ∧
      (d.dilate (asymptoticConeRadius hcomparison a.1) a.property).ambientChart x = a.1 ∧
      a.1 ∈ (d.dilate (asymptoticConeRadius hcomparison a.1) a.property).ambientChart.target := by
  obtain ⟨d, z, hz⟩ := hcover (asymptoticConeNormalize hcomparison a)
  let x : UnitSliceAmbient n := z.1.1
  have hx : x ∈ d.ambientChart.source := z.1.2
  have hunit : d.ambientChart x = (asymptoticConeNormalize hcomparison a).1 :=
    congrArg Subtype.val hz
  have hvalue : (d.dilate (asymptoticConeRadius hcomparison a.1) a.property).ambientChart x = a.1 := by
    rw [d.dilate_apply, hunit]
    change asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison a.1)
      (asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison a.1)⁻¹ a.1) = a.1
    rw [asymptoticConeDilation_mul, mul_inv_cancel₀ a.property.ne', asymptoticConeDilation_one]
  have htarget :=
    (d.dilate (asymptoticConeRadius hcomparison a.1) a.property).ambientChart.map_source hx
  rw [hvalue] at htarget
  exact ⟨d, x, hx, hvalue, htarget⟩

end Poincare.AncientVolume.ScalarRatio
