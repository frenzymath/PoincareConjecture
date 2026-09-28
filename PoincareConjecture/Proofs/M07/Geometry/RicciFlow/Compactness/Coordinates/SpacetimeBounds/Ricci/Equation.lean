import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.PullbackRicci
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.TimeDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle BigOperators

namespace PoincareConjecture.SpacetimeBounds

theorem metricTwoJet_congr_of_eventuallyEq {n : ℕ}
    {B B' : EuclideanSpace ℝ (Fin n) → MetricCoefficient n} {x : EuclideanSpace ℝ (Fin n)}
    (h : B =ᶠ[𝓝 x] B') : metricTwoJet B x = metricTwoJet B' x := by
  simp only [metricTwoJet, h.eq_of_nhds, h.fderiv_eq, (h.fderiv (𝕜 := ℝ)).fderiv_eq]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem jetRicci_metricTwoJet_pullback {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (u v : EuclideanSpace ℝ (Fin n)) :
    jetRicci (metricTwoJet (g.pullbackCoefficients e) x) u v =
      D.ricci (e x) (mfderiv (𝓡 n) (𝓡 n) e x u) (mfderiv (𝓡 n) (𝓡 n) e x v) := by
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    hU hx (g.pullbackCoefficients e) hcoeff (fun y _ u v => g.symm (e y) _ _)
    (fun y hy w hw => by
      apply g.pos (e y)
      intro hz
      apply hw
      apply (hi y hy).injective
      rw [map_zero]
      convert! hz using 1)
  have hmetric (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) (u v) :
      gE.inner y u v = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y u) (mfderiv (𝓡 n) (𝓡 n) e y v) :=
    congrArg (fun B => B u v) (heq y hy)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  rw [← metricTwoJet_congr_of_eventuallyEq hB, jetRicci_metricTwoJet DE]
  exact DE.ricci_eq_of_local_isometry D hV (he.mono hVU) hmetric hxV u v

theorem deriv_pullbackCoefficients_eq_ricciFlowOperator {J : Set ℝ} (F : RicciFlow n M J)
    (hJ : IsOpen J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    deriv (fun s => (F.metric s).pullbackCoefficients e x) t =
      ricciFlowOperator n (metricTwoJet ((F.metric t).pullbackCoefficients e) x) := by
  classical
  rw [bilinear_eq_sum_dual (EuclideanSpace.basisFun (Fin n) ℝ)
    (deriv (fun s => (F.metric s).pullbackCoefficients e x) t)]
  unfold ricciFlowOperator
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [F.deriv_pullbackCoefficients_apply hJ hU he ht hx,
    jetRicci_metricTwoJet_pullback (F.connection t) hU he hi hx]

end PoincareConjecture.SpacetimeBounds
