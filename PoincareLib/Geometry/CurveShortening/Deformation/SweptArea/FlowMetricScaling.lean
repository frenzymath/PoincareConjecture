import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.SweptArea.MetricScaling
import PoincareLib.Geometry.RicciFlow.CurveShortening.Estimates.Pointwise
import PoincareLib.Geometry.RicciFlow.MetricComparison

/-!
# Area comparison between included flow times

The actual-flow metric-scaling step of Claim 19.23, printed pp. 453-454.
M62's unit-input Ricci bound is normalized before the closed M07 metric
comparison is applied. The same factor works for base and product flows
when their ambient bounds use the same K2.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) {K0 K1 K2 : ℝ}

/-- Normalize M63's retained Ricci bound to arbitrary tangent vectors;
the metric-comparison step of Claim 19.23, pp. 453-454. -/
theorem m65Ricci_quadratic_bound (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Set.Icc a b) (x : M) (v : TangentSpace (𝓡 n) x) :
    |(F.connection t).ricci x v v| ≤ K2 * (F.metric t).inner x v v := by
  have h := M62.tensor_abs_le_of_unit_bound (F.metric t) (F.connection t).ricciEvaluation
    (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t)) x (K := K2)
    (fun w hw => bounds.ricci t ht x (w 0) (w 1) (hw 0) (hw 1)) ![v, v]
  have hnonneg := ((F.metric t).toRiemannianMetric.toCore x).re_inner_nonneg v
  change 0 ≤ (F.metric t).inner x v v at hnonneg
  simpa only [LeviCivitaData.ricciEvaluation, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, RiemannianMetric.tangentNorm,
    Real.mul_self_sqrt hnonneg] using h

/-- The exact K2 bound compares actual quadratic forms in either time
order, including the endpoints; Claim 19.23, pp. 453-454. -/
theorem m65FlowMetric_comparison (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x v v ≤
      Real.exp ((2 * K2) * |t - s|) * (F.metric s).inner x v v :=
  (F.metric_inner_self_exp_bounds (convex_Icc a b) Set.Subset.rfl x v K2
    (fun _ hr => m65Ricci_quadratic_bound F bounds hr x v) hs ht).2

/-- Pointwise flow-area scaling with the ambient K2, independent of the
map and, for the retained products, circumference; Claim 19.23, pp. 453-454. -/
theorem m65FlowAreaDensity_scaling (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity (F.metric t) f z ≤
      Real.exp ((2 * K2) * |t - s|) * m60AreaDensity (F.metric s) f z :=
  m65AreaDensityScaling_of_metric_comparison (F.metric s) (F.metric t)
    (Real.exp_nonneg _) (m65FlowMetric_comparison F bounds hs ht) f z

/-- Integrated flow-area comparison, with integrable Jacobians at both
actual metrics; Claim 19.23, pp. 453-454. -/
theorem m65FlowArea_scaling (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (f : LoopPlane → M) (domain : Set LoopPlane)
    (hsint : IntegrableOn (m60AreaDensity (F.metric s) f) domain volume)
    (htint : IntegrableOn (m60AreaDensity (F.metric t) f) domain volume) :
    (∫ z in domain, m60AreaDensity (F.metric t) f z) ≤
      Real.exp ((2 * K2) * |t - s|) * ∫ z in domain, m60AreaDensity (F.metric s) f z :=
  m65AreaScaling_of_metric_comparison (F.metric s) (F.metric t) (Real.exp_nonneg _)
    (m65FlowMetric_comparison F bounds hs ht) f domain hsint htint

end PoincareMT
