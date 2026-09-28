import PoincareConjecture.Proofs.M47.LimitNoncollapseMovingCurvature
import PoincareConjecture.Proofs.M34.Standard.ScalarMetricJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence S J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitNoncollapse_eventually_point_scalar
    (P : M47Predecessors.{u}) (t : ℝ) (ht : t ∈ J)
    (x : G.limit.sliceCarrier.carrier) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      t ∈ Icc (-G.exhaustion.time k) 0 ∧ x ∈ G.exhaustion.space k ∧
      ∀ hs : t ∈ Icc (-G.exhaustion.time k) 0,
        |(S.flow (G.subsequence k)).scalar ((G.embedding k).pointMap t hs x) /
          S.scale (G.subsequence k) - (G.limit.flow.connection t).scalarCurvature x| <
            epsilon := by
  classical
  let c := extChartAt (𝓡 3) x
  let p : E := c x
  have hp : p ∈ c.target := mem_extChartAt_target x
  have hpx : c.symm p = x := extChartAt_to_inv x
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_singleton (x := x))
  have hdomain : ∀ᶠ k in atTop,
      t ∈ Icc (-G.exhaustion.time k) 0 ∧ x ∈ G.exhaustion.space k := by
    filter_upwards [G.exhaustion.time_cofinal {t} isCompact_singleton
      (singleton_subset_iff.mpr ht), eventually_ge_atTop j] with k hk hjk
    exact ⟨hk (mem_singleton t), G.exhaustion.space_increasing hjk (hj (mem_singleton x))⟩
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ :=
    G.limit.carrier.exists_local_coordinate_realization (G.limit.flow.metric t) x t p hp
  have hg := Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  have hreal : ∀ᶠ k in atTop,
      ∃ gd : Σ g : RiemannianMetric 3 E, LeviCivitaData g,
        ∀ᶠ y in 𝓝 p, ∀ a b : Fin 3,
          gd.1.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) =
            blowupPullbackCoefficient (G.embedding k) x a b (t, y) := by
    filter_upwards [hdomain] with k hk
    obtain ⟨gk, Dk, Vk, hVko, hpVk, _, heqk⟩ :=
      (G.embedding k).exists_local_coordinate_realization (G.exhaustion.space_open k)
        x hk.1 p ⟨hp, hpx.symm ▸ hk.2⟩
    exact ⟨⟨gk, Dk⟩, Filter.Eventually.mono (hVko.mem_nhds hpVk) heqk⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hjets (r : ℕ) (_hr : r ≤ 2) (a b : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (gd k).1.inner y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)
        atTop (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)) := by
    erw [G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
      x _ t p g hg r a b]
    apply (limitNoncollapse_tendsto_moving_spatial_jets G P x isCompact_singleton
      (singleton_subset_iff.mpr ht) tendsto_id (fun _ => mem_singleton t)
      (mem_singleton t) hp (tendsto_const_nhds (x := (t, p))) r a b).congr'
    filter_upwards [hgd] with k hk
    have he : (fun y => (gd k).1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p]
          (fun y => blowupPullbackCoefficient (G.embedding k) x a b (t, y)) :=
      hk.mono (fun y hy => hy a b)
    exact (he.iteratedFDeriv ℝ r).self_of_nhds.symm
  have hscalar := LeviCivitaData.tendsto_scalarCurvature_of_finite_scalar_metric_jets
    (fun k => (gd k).2) D p (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis hjets
  rw [G.limit.carrier.scalarCurvature_eq_of_frozen_coordinate_germ
    (G.limit.flow.metric t) (G.limit.flow.connection t) x t p hp g D hg, hpx] at hscalar
  have herror := (Metric.tendsto_atTop.mp hscalar) epsilon hepsilon
  obtain ⟨N, hN⟩ := herror
  filter_upwards [hdomain, hgd, eventually_ge_atTop N] with k hk hkg hkN
  refine ⟨hk.1, hk.2, ?_⟩
  intro hs
  have hread := ((G.embedding k).curvatures_eq_of_coordinate_germ
    (G.exhaustion.space_open k) x hs p ⟨hp, hpx.symm ▸ hk.2⟩
    (gd k).1 (gd k).2 hkg).1
  rw [hpx] at hread
  rw [← hread]
  exact hN k hkN

end PoincareConjecture.M47
