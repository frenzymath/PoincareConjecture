import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

theorem m23AllTimeCurvatureControl_of_local
    {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hlocal : M23LocalCurvatureEstimate S) :
    M23AllTimeCurvatureControl S := by
  intro r hr
  obtain ⟨C, hC, hbound⟩ := hlocal r hr
  refine ⟨C, hC, ?_⟩
  intro k
  let B := S.term k
  let Crr := B.carrier
  letI : TopologicalSpace Crr.carrier := Crr.topologicalSpace
  letI : MeasurableSpace Crr.carrier := Crr.measurableSpace
  letI : BorelSpace Crr.carrier := Crr.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Crr.carrier := Crr.chartedSpace
  letI : IsManifold (𝓡 3) ∞ Crr.carrier := Crr.isManifold
  letI : T2Space Crr.carrier := Crr.t2Space
  letI : T3Space Crr.carrier := Crr.t3Space
  letI : SecondCountableTopology Crr.carrier := Crr.secondCountable
  letI : ConnectedSpace Crr.carrier := B.connectedSpace
  change ∀ t : ℝ, t ≤ 0 → ∀ x : Crr.carrier,
    x ∈ Crr.metricBall (B.flow.flow.metric 0) B.base r →
      |(B.flow.flow.connection t).curvatureTensorNorm x| ≤ C
  intro t ht x hx
  rw [abs_of_nonneg (show 0 ≤ (B.flow.flow.connection t).curvatureTensorNorm x from
    Real.sqrt_nonneg _)]
  exact (P.past_norm_le_scalar Crr.carrier B.flow t 0 ht le_rfl x).trans
    (hbound k x hx)

end PoincareConjecture
