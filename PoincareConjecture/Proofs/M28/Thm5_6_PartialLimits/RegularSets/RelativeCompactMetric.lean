import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.RelativeChartMetric
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.RelativeMetricReadout

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}

theorem eventually_compact_relative_inner_bounds (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (K : Set G.limitCarrier.carrier), IsCompact K →
      ∀ tau : ℝ, 0 < tau → ∀ᶠ k in atTop, ∀ x ∈ K,
        ∀ v : TangentSpace (𝓡 n) x,
          (1 + tau)⁻¹ * G.limitMetric.inner x v v ≤
            (g (G.subsequence k)).inner (G.embedding k x)
              (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) x v)
              (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) x v) ∧
          (g (G.subsequence k)).inner (G.embedding k x)
            (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) x v)
            (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) x v) ≤
              (1 + tau) * G.limitMetric.inner x v v := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let : LocallyCompactSpace G.limitCarrier.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier
  intro K hK tau htau
  obtain ⟨s, C, hC, hcover⟩ :=
    hK.exists_finite_extChart_cover (𝓡 n) isOpen_univ (subset_univ _)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  obtain ⟨j, hj⟩ := hK.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) hmono.directed_le
  have htail := s.finite_toSet.eventually_all.mpr (fun q hq =>
    G.eventually_chart_relative_inner_bounds q _
      (hC q hq).2.2.2.2.1 (hC q hq).2.2.2.2.2 tau htau)
  filter_upwards [htail, eventually_ge_atTop j] with k hk hjk
  intro x hx v
  obtain ⟨q, hq, hxC⟩ := mem_iUnion₂.mp (hcover hx)
  have hxC' : x ∈ C q := interior_subset hxC
  have hxsource : x ∈ (extChartAt (𝓡 n) q).source := ((hC q hq).2.2.2.1 hxC').1
  exact G.limitMetric.relative_inner_bounds_of_chart (g (G.subsequence k)) hxsource
    ((G.embedding_smooth k ⟨x, hmono hjk (hj hx)⟩).mdifferentiableAt (by simp))
    (hk q hq _ (mem_image_of_mem _ hxC')) v

end PoincareConjecture.M28.RegularPointedMetricConvergence
