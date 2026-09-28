import PoincareConjecture.Proofs.M34.Thm12_5_Existence.InitialLimitJetConvergence
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.ApproximationRealization
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.InteriorCoefficientLimit

open SpacetimeBounds

variable {g0 : StandardInitialMetric} {A : CompactCapApproximation g0}
  (G : InteriorCoefficientLimit A)



theorem initialFlow_curvature_le (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 A.time) (x : StandardCapSpace) :
    ((G.initialFlow P).connection t).curvatureTensorNorm x ≤ A.curvature_bound 0 := by
  classical
  have hex (k : ℕ) :
      ∃ data : Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g,
        x ∈ compactCapSource g0 (G.subsequence k) →
          metricTwoJet data.1.euclideanCoefficients x =
              metricTwoJet (A.coefficients (G.subsequence k) t) x ∧
            data.2.curvatureTensorNorm x ≤ A.curvature_bound 0 := by
    by_cases hx : x ∈ compactCapSource g0 (G.subsequence k)
    · obtain ⟨g, D, hjet, hnorm⟩ := A.exists_metric_twoJet_realization
        (G.subsequence k) ⟨ht.1, ht.2.le⟩ hx
      exact ⟨⟨g, D⟩, fun _ => ⟨hjet, hnorm⟩⟩
    · exact ⟨G.limitMetricConnection P t, fun h => (hx h).elim⟩
  choose data hdata using hex
  have hsource : ∀ᶠ k : ℕ in atTop, x ∈ compactCapSource g0 (G.subsequence k) := by
    filter_upwards [G.strictMono.tendsto_atTop.eventually
      (eventually_compact_subset_double_source g0 (isCompact_singleton (x := x)))] with k hk
    exact hk (mem_singleton x)
  have hjet : Tendsto (fun k => metricTwoJet (data k).1.euclideanCoefficients x) atTop
      (𝓝 (metricTwoJet (G.limitMetric P t).euclideanCoefficients x)) := by
    apply (G.metricTwoJet_tendsto P ht x).congr'
    filter_upwards [hsource] with k hk
    exact (hdata k hk).1.symm
  have hnorm := LeviCivitaData.tendsto_curvatureTensorNorm_of_metric_jets
    (fun k => (data k).2) (G.limitConnection P t) x
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    hjet.fst_nhds hjet.snd_nhds.fst_nhds hjet.snd_nhds.snd_nhds
  apply le_of_tendsto hnorm
  filter_upwards [hsource] with k hk
  exact (hdata k hk).2



theorem initialFlow_abs_curvature_le (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 A.time) (x : StandardCapSpace) :
    |((G.initialFlow P).connection t).curvatureTensorNorm x| ≤ A.curvature_bound 0 := by
  have hn : 0 ≤ ((G.initialFlow P).connection t).curvatureTensorNorm x :=
    Real.sqrt_nonneg _
  rw [abs_of_nonneg hn]
  exact G.initialFlow_curvature_le P ht x

end PoincareConjecture.M34.InteriorCoefficientLimit
