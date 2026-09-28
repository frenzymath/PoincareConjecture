import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.CanonicalDomain









set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow

noncomputable def pullbackWithConnection
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {J : Set ℝ} (F : RicciFlow n N J) (e : M → N)
    (he : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ e)
    (D : ∀ t, LeviCivitaData ((F.metric t).pullbackOfLocalDiffeomorph e he)) :
    RicciFlow n M J where
  metric t := (F.metric t).pullbackOfLocalDiffeomorph e he
  connection := D
  interval := F.interval
  nontrivial := F.nontrivial
  smooth := F.smooth.pullbackOfLocalDiffeomorph e he
  equation t ht x v w := by
    have hRicci := (D t).ricci_eq_of_local_isometry (F.connection t)
      isOpen_univ he.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x) v w
    rw [hRicci]
    exact F.equation t ht (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w)

noncomputable def pullbackToCanonicalDomain
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {J : Set ℝ} (F : RicciFlow n N J)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U]
    (e : U → N)
    (he : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ e) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    RicciFlow n U J := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  exact F.pullbackWithConnection e he (fun t =>
    RiemannianMetric.canonicalMetricLeviCivitaData U hU
      ((F.metric t).pullbackOfLocalDiffeomorph e he))

@[simp] theorem pullbackToCanonicalDomain_metric
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {J : Set ℝ} (F : RicciFlow n N J)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U]
    (e : U → N)
    (he : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ e) (t : ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    (F.pullbackToCanonicalDomain U hU e he).metric t =
      (F.metric t).pullbackOfLocalDiffeomorph e he := rfl

end PoincareConjecture.RicciFlow
