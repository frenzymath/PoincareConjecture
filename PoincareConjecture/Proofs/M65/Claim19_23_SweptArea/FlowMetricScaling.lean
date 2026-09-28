import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.MetricScaling
import PoincareConjecture.Proofs.M62.Cor0_3_PointwiseBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison










set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) {K0 K1 K2 : ℝ}



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



theorem m65FlowMetric_comparison (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x v v ≤
      Real.exp ((2 * K2) * |t - s|) * (F.metric s).inner x v v :=
  (F.metric_inner_self_exp_bounds (convex_Icc a b) Set.Subset.rfl x v K2
    (fun _ hr => m65Ricci_quadratic_bound F bounds hr x v) hs ht).2



theorem m65FlowAreaDensity_scaling (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity (F.metric t) f z ≤
      Real.exp ((2 * K2) * |t - s|) * m60AreaDensity (F.metric s) f z :=
  m65AreaDensityScaling_of_metric_comparison (F.metric s) (F.metric t)
    (Real.exp_nonneg _) (m65FlowMetric_comparison F bounds hs ht) f z



theorem m65FlowArea_scaling (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (f : LoopPlane → M) (domain : Set LoopPlane)
    (hsint : IntegrableOn (m60AreaDensity (F.metric s) f) domain volume)
    (htint : IntegrableOn (m60AreaDensity (F.metric t) f) domain volume) :
    (∫ z in domain, m60AreaDensity (F.metric t) f z) ≤
      Real.exp ((2 * K2) * |t - s|) * ∫ z in domain, m60AreaDensity (F.metric s) f z :=
  m65AreaScaling_of_metric_comparison (F.metric s) (F.metric t) (Real.exp_nonneg _)
    (m65FlowMetric_comparison F bounds hs ht) f domain hsint htint

end PoincareConjecture
