import PoincareConjecture.Proofs.M15.Prop8_2_CylinderFlow
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T r : ℝ} {x : (G.slices T).Point} {K : SpacetimeInterval}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T2Space C] [SecondCountableTopology C]




theorem actualBallCylinder_terminal_edist_le
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (F : RicciFlow n C K.domain) (hmetric : F.metric = B.metric.metric)
    (hRm : ∀ (t : (G.timeIntervals.interval K).Point) (c : C),
      (F.connection t.val).curvatureTensorNorm c =
        horizontalCurvatureNorm G.leafwise (B.embedding.toSpacetime (t, c)))
    {s : ℝ} (hs : s ∈ K.domain) (c d : C) :
    (G.slices T).metricOnPoints.edist (B.source_map c) (B.source_map d) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (r⁻¹) ^ 2 * (T - s))) *
        (F.metric s).edist c d := by
  have hsT : s ≤ T := by
    rw [B.interval_domain] at hs
    exact hs.2
  have hsource : ContMDiff (𝓡 n) (𝓡 n) 1 B.source_map :=
    contMDiffOn_univ.mp (B.source_map_smooth.of_le (by simp))
  apply RiemannianMetric.edist_le_mul_of_tangentNorm_mfderiv_le
    (F.metric s) (G.slices T).metricOnPoints hsource (Real.exp_pos _) _ c d
  intro z v
  have hbound : ∀ τ ∈ Set.Icc s T,
      (F.connection τ).curvatureTensorNorm z ≤ (r⁻¹) ^ 2 := by
    intro τ hτ
    have hτK : τ ∈ K.domain := F.interval.out hs B.base_mem hτ
    rw [hRm ⟨τ, hτK⟩ z]
    exact B.curvature_bound ⟨τ, hτK⟩ z
  have hnorm : (G.slices T).metricOnPoints.tangentNorm (B.source_map z)
      (mfderiv (𝓡 n) (𝓡 n) B.source_map z v) = (F.metric T).tangentNorm z v := by
    rw [hmetric]
    exact congrArg Real.sqrt (actualBallCylinder_terminal_metric_pullback hM12 B z v v)
  rw [hnorm]
  exact (M04.tangentNorm_comparison_at_of_curvature_bound F hs B.base_mem hsT
    (sq_nonneg _) z hbound v).2

end PoincareConjecture.Proofs.M15
