import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.FiniteChartBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
  {ι : Type*} [Finite ι]




theorem exists_limit_finite_chart_bounds (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : ι → G.limitCarrier.carrier) (K : ι → Set (EuclideanSpace ℝ (Fin n))),
      (∀ i, IsCompact (K i)) → (∀ i, K i ⊆ (extChartAt (𝓡 n) (q i)).target) →
      ∀ m : ℕ, ∃ a b B : ℝ, 0 < a ∧ 0 < b ∧ 1 ≤ B ∧
        ∀ i x, x ∈ K i →
          (∀ v : EuclideanSpace ℝ (Fin n),
            a * ‖v‖ ^ 2 ≤ G.limitMetric.pullbackCoefficients
              (extChartAt (𝓡 n) (q i)).symm x v v ∧
            G.limitMetric.pullbackCoefficients
              (extChartAt (𝓡 n) (q i)).symm x v v ≤ b * ‖v‖ ^ 2) ∧
          ∀ r ≤ m, ‖iteratedFDeriv ℝ r (G.limitMetric.pullbackCoefficients
            (extChartAt (𝓡 n) (q i)).symm) x‖ ≤ B := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q K hK htarget m
  obtain ⟨a, b, B, ha, hb, hB, htail⟩ :=
    G.exists_eventual_finite_chart_bounds q K hK htarget m
  refine ⟨a, b, B, ha, hb, hB, ?_⟩
  intro i x hx
  constructor
  · intro v
    have hcoeff := (G.tendstoUniformlyOn_chart_coefficients
      (q i) (K i) (hK i) (htarget i)).tendsto_at hx
    have heval : Continuous (fun B : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => B v v) :=
      (continuous_id.clm_apply continuous_const).clm_apply continuous_const
    have hvalue := heval.continuousAt.tendsto.comp hcoeff
    exact ⟨ge_of_tendsto hvalue (htail.mono fun k hk => (hk i x hx).1 v |>.1),
      le_of_tendsto hvalue (htail.mono fun k hk => (hk i x hx).1 v |>.2)⟩
  · intro r hr
    exact le_of_tendsto
      (((G.metric_jets (q i) r (K i) (hK i) (htarget i)).tendsto_at hx).norm)
      (htail.mono fun k hk => (hk i x hx).2 r hr)

end PoincareConjecture.M28.RegularPointedMetricConvergence
