import PoincareConjecture.Definitions.Ch04.Harnack
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import Mathlib.Topology.Maps.Proper.Basic











set_option autoImplicit false

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.M30

universe u



theorem metricComplete_of_proper_height_and_metric_translations
    {n : ℕ} {P : Type u} [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
    [IsManifold (𝓡 n) ∞ P] [T3Space P]
    (g : RiemannianMetric n P)
    {f : P → ℝ} {Phi : ℝ → P → P} {K : Set P}
    (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f)
    (hproper : IsProperMap f) (hK : IsCompact K)
    (hPhi : ∀ t : ℝ, MDifferentiable (𝓡 n) (𝓡 n) (Phi t))
    (hmetric : ∀ (t : ℝ) (x : P) (v w : TangentSpace (𝓡 n) x),
      g.inner (Phi t x) (mfderiv (𝓡 n) (𝓡 n) (Phi t) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Phi t) x w) = g.inner x v w)
    (hheight : ∀ (t : ℝ) (x : P), f (Phi t x) = f x + t)
    (hcover : ∀ x : P, ∃ t : ℝ, Phi t x ∈ K) : MetricComplete g := by
  obtain ⟨B, hB, hbound⟩ := g.exists_metric_derivative_bound_on_compact hf hK
  have hglobal (x : P) (v : TangentSpace (𝓡 n) x) :
      |mvfderiv (𝓡 n) f x v| ≤ B * g.tangentNorm x v := by
    obtain ⟨t, ht⟩ := hcover x
    have heq : f ∘ Phi t = fun y => f y + t := funext (hheight t)
    have hderiv : mvfderiv (𝓡 n) f (Phi t x)
        (mfderiv (𝓡 n) (𝓡 n) (Phi t) x v) = mvfderiv (𝓡 n) f x v := by
      rw [← mvfderiv_comp_apply x (hf.mdifferentiable (by simp) (Phi t x))
        (hPhi t x) v, heq]
      rw [mvfderiv_fun_add (hf.mdifferentiable (by simp) x) mdifferentiableAt_const,
        mvfderiv_const]
      simp
    have hnorm : g.tangentNorm (Phi t x) (mfderiv (𝓡 n) (𝓡 n) (Phi t) x v) =
        g.tangentNorm x v := by
      unfold RiemannianMetric.tangentNorm
      rw [hmetric t x v v]
    simpa only [hderiv, hnorm] using
      hbound (Phi t x) ht (mfderiv (𝓡 n) (𝓡 n) (Phi t) x v)
  let C : ℝ≥0 := ⟨B + 1, by linarith⟩
  have hC : 0 < C := by change 0 < B + 1; linarith
  have hgrad (x : P) (v : TangentSpace (𝓡 n) x) :
      |mvfderiv (𝓡 n) f x v| ≤ C * g.tangentNorm x v :=
    (hglobal x v).trans (mul_le_mul_of_nonneg_right
      (show B ≤ (C : ℝ) by change B ≤ B + 1; linarith) (Real.sqrt_nonneg _))
  let : RiemannianBundle (TangentSpace (𝓡 n) : P → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace P := EMetricSpace.ofRiemannianMetric (𝓡 n) P
  have hLip : LipschitzWith C f := by
    intro x y
    change EDist.edist (f x) (f y) ≤ (C : ℝ≥0∞) * g.edist x y
    exact g.edist_le_mul_edist_of_derivative_bound (hf.of_le (by simp)) hC hgrad x y
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
    (hLip.uniformContinuous.comp_cauchySeq hu)
  have hyc : MapClusterPt y (map u atTop) f := by
    simpa only [MapClusterPt, map_map, Function.comp_def] using hy.mapClusterPt
  obtain ⟨x, _, hx⟩ := hproper.clusterPt_of_mapClusterPt hyc
  exact ⟨x, le_nhds_of_cauchy_adhp hu hx⟩

end PoincareConjecture.M30
