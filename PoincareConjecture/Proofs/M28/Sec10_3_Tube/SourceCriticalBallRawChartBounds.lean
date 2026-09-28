import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawCoefficients
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.FiniteChartBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E)
  (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
  (phi : ℕ → ℕ)
  (G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k)))
  {ι : Type*} [Finite ι]

theorem exists_eventual_regularRawStage_finite_chart_bounds :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : ι → G.limitCarrier.carrier) (K : ι → Set (EuclideanSpace ℝ (Fin 3)))
      (j : ℕ), (∀ i, IsCompact (K i)) →
      (∀ i, K i ⊆ (extChartAt (𝓡 3) (q i)).target) →
      (∀ i y, y ∈ K i → (extChartAt (𝓡 3) (q i)).symm y ∈ G.exhaustion j) →
      ∀ m : ℕ, ∃ a b B : ℝ, 0 < a ∧ 0 < b ∧ 1 ≤ B ∧
        ∀ᶠ k in atTop, ∀ i y, y ∈ K i →
          (∀ v : EuclideanSpace ℝ (Fin 3),
            a * ‖v‖ ^ 2 ≤ (H.normalizedSliceMetric (phi (G.subsequence k))).pullbackCoefficients
              (H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘
                (extChartAt (𝓡 3) (q i)).symm) y v v ∧
            (H.normalizedSliceMetric (phi (G.subsequence k))).pullbackCoefficients
              (H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘
                (extChartAt (𝓡 3) (q i)).symm) y v v ≤ b * ‖v‖ ^ 2) ∧
          ∀ r ≤ m, ‖iteratedFDeriv ℝ r
            ((H.normalizedSliceMetric (phi (G.subsequence k))).pullbackCoefficients
              (H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘
                (extChartAt (𝓡 3) (q i)).symm)) y‖ ≤ B := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q K j hK htarget hstage m
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  obtain ⟨a, b, B, ha, hb, hB, htail⟩ :=
    G.exists_eventual_finite_chart_bounds q K hK htarget m
  refine ⟨a, b, B, ha, hb, hB, ?_⟩
  filter_upwards [htail, eventually_ge_atTop j] with k hk hjk
  intro i y hy
  have heq := H.regularRawStage_coefficients_germ T A1 hA1 phi G k (q i) y
    (htarget i hy) (hmono hjk (hstage i y hy))
  constructor
  · intro v
    rw [heq.eq_of_nhds]
    exact (hk i y hy).1 v
  · intro r hr
    rw [(heq.iteratedFDeriv ℝ r).eq_of_nhds]
    exact (hk i y hy).2 r hr

theorem eventually_regularRawStage_finite_chart_jet_error :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : ι → G.limitCarrier.carrier) (K : ι → Set (EuclideanSpace ℝ (Fin 3)))
      (j : ℕ), (∀ i, IsCompact (K i)) →
      (∀ i, K i ⊆ (extChartAt (𝓡 3) (q i)).target) →
      (∀ i y, y ∈ K i → (extChartAt (𝓡 3) (q i)).symm y ∈ G.exhaustion j) →
      ∀ (m : ℕ) (delta : ℝ), 0 < delta →
        ∀ᶠ k in atTop, ∀ i y, y ∈ K i → ∀ r ≤ m,
          ‖iteratedFDeriv ℝ r
              ((H.normalizedSliceMetric (phi (G.subsequence k))).pullbackCoefficients
                (H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘
                  (extChartAt (𝓡 3) (q i)).symm)) y -
            iteratedFDeriv ℝ r
              (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm) y‖ ≤ delta := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q K j hK htarget hstage m delta hdelta
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  filter_upwards [G.eventually_finite_chart_jet_error q K hK htarget m delta hdelta,
    eventually_ge_atTop j] with k hk hjk
  intro i y hy r hr
  have heq := H.regularRawStage_coefficients_germ T A1 hA1 phi G k (q i) y
    (htarget i hy) (hmono hjk (hstage i y hy))
  rw [(heq.iteratedFDeriv ℝ r).eq_of_nhds]
  exact hk i y hy r hr

end PoincareConjecture.M28.CounterexampleNeckFamily
