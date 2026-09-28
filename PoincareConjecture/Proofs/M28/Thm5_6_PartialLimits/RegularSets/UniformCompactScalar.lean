import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.UniformChartScalar
import PoincareConjecture.Proofs.M28.Mathlib.FiniteChartCover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k}




theorem tendstoUniformlyOn_scalarCurvature
    (G : RegularPointedMetricConvergence g p) (D : ∀ k, LeviCivitaData (g k)) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (D0 : LeviCivitaData G.limitMetric) (K : Set G.limitCarrier.carrier),
      IsCompact K → TendstoUniformlyOn
        (fun k x => (D (G.subsequence k)).scalarCurvature (G.embedding k x))
        D0.scalarCurvature atTop K := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let : LocallyCompactSpace G.limitCarrier.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) G.limitCarrier.carrier
  intro D0 K hK
  obtain ⟨s, C, hC, hcover⟩ :=
    hK.exists_finite_extChart_cover (𝓡 3) isOpen_univ (subset_univ _)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro delta hdelta
  have htail : ∀ q ∈ s, ∀ᶠ k in atTop,
      ∀ x ∈ (extChartAt (𝓡 3) q) '' C q,
        dist (D0.scalarCurvature ((extChartAt (𝓡 3) q).symm x))
          ((D (G.subsequence k)).scalarCurvature
            (G.embedding k ((extChartAt (𝓡 3) q).symm x))) < delta := by
    intro q hq
    exact Metric.tendstoUniformlyOn_iff.mp
      (G.tendstoUniformlyOn_chart_scalarCurvature D D0 q _
        (hC q hq).2.2.2.2.1 (hC q hq).2.2.2.2.2) delta hdelta
  filter_upwards [s.finite_toSet.eventually_all.mpr htail] with k hk
  intro x hx
  obtain ⟨q, hq, hxC⟩ := mem_iUnion₂.mp (hcover hx)
  have hxC' : x ∈ C q := interior_subset hxC
  have hinverse : (extChartAt (𝓡 3) q).symm ((extChartAt (𝓡 3) q) x) = x :=
    (extChartAt (𝓡 3) q).left_inv ((hC q hq).2.2.2.1 hxC').1
  simpa only [hinverse] using hk q hq _ (mem_image_of_mem _ hxC')




theorem exists_eventual_compact_scalar_bound
    (G : RegularPointedMetricConvergence g p) (D : ∀ k, LeviCivitaData (g k)) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (_D0 : LeviCivitaData G.limitMetric) (K : Set G.limitCarrier.carrier), IsCompact K →
      ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
        |(D (G.subsequence k)).scalarCurvature (G.embedding k x)| ≤ B := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 K hK
  simpa only [Real.norm_eq_abs] using
    (G.tendstoUniformlyOn_scalarCurvature D D0 K hK).exists_eventual_norm_bound hK
      D0.continuous_scalarCurvature.continuousOn

end PoincareConjecture.M28.RegularPointedMetricConvergence
