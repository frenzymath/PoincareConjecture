import PoincareConjecture.Proofs.M47.TerminalCommonIntervalUnitTangent
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalExhaustionMap
import PoincareConjecture.Proofs.M47.TerminalGermsMetricComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing PoincareConjecture.ChartDistance
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem terminalCommonInterval_source_tangent
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 3))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    [T2Space (Quotient O.setoid)]
    (E : ℕ → Set (Quotient O.setoid)) (hE : ∀ k, IsOpen (E k))
    (hmono : Monotone E) (hcover : (⋃ k, E k) = univ)
    {N : ℕ → Type u} [∀ k, TopologicalSpace (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)]
    (f : ∀ k, Quotient O.setoid → N k)
    (hf : letI := quotientChartedSpace U hU O
      ∀ k, IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (E k))
    (h : ∀ k, RiemannianMetric 3 (N k))
    (g : ∀ i, CanonicalMetric U hU i) (hg : CompatibleMetrics U hU O g)
    (B : ℕ → EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hB : ∀ i, ContinuousOn (B i) (U i))
    (hcoeff : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ i (x : Piece U i) v w, (g i).inner x v w = B i x v w)
    (hconv : ∀ i K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => (h k).pullbackCoefficients (chartParametrization U hU (f k ∘ O.include i)))
      (B i) atTop K) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∀ K : Set (Quotient O.setoid), IsCompact K → ∀ lambda : ℝ,
      0 < lambda → lambda < 1 → ∀ᶠ k in atTop,
        K ⊆ E k ∧ ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
          lambda * (quotientMetric U hU O hO g hg).tangentNorm x v ≤
            (h k).tangentNorm (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v) ∧
          (h k).tangentNorm (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v) ≤
            lambda⁻¹ * (quotientMetric U hU O hO g hg).tangentNorm x v := by
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have herror := source_exhaustion_uniform_metric_error U hU O hO hE hmono hcover f hf
    (fun k _ => h k) (fun i _ => g i) (fun _ => hg)
    (J := {0}) (fun i p => B i p.2)
    (fun i => (hB i).comp continuous_snd.continuousOn (fun _ hp => hp.2))
    (fun i _ _ x => hcoeff i x) (by
      intro i K hK hKU
      have hsub : Prod.snd '' K ⊆ U i := by
        rintro _ ⟨p, hp, rfl⟩
        exact (hKU hp).2
      exact ((hconv i (Prod.snd '' K) (hK.image continuous_snd) hsub).comp Prod.snd).mono
        (subset_preimage_image Prod.snd K))
  intro K hK lambda hlambda hlambda_lt
  obtain ⟨j, hj⟩ := hK.elim_directed_cover E hE
    (by rw [hcover]; exact subset_univ _) hmono.directed_le
  have hdelta : 0 < (1 - lambda ^ 2) / 2 := by nlinarith
  filter_upwards [eventually_ge_atTop j,
    herror K {0} hK isCompact_singleton Subset.rfl _ hdelta] with k hjk hk
  refine ⟨hj.trans (hmono hjk), ?_⟩
  intro x hx v
  exact terminalCommonInterval_tangent_of_unit_error
    (quotientMetric U hU O hO g hg) (h k) (f k) x hlambda hlambda_lt
    (hk 0 (mem_singleton 0) x hx) v

end PoincareConjecture.M47
