import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.AncientAction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Ancient









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem exists_reducedLength_eq_spatialInfimum (K : AncientKappaSolution 2 M)
    (p : M) {tau : ℝ} (htau : 0 < tau) :
    ∃ q : M, reducedLength K.flow 0 p q tau = K.spatialReducedLengthInfimum p tau := by
  classical
  let : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
  obtain ⟨γ, m, t, x, Q, w, hγ, hγ0, ht, ht0, htend, hQ, hprimitive, hbound⟩ :=
    K.exists_spatial_minimizing_weak_action p htau
  have hle := K.reducedLength_le_finite_chart_action htau t ht ht0 htend
    γ hγ.continuousOn x
    (fun i s hs => (hQ i).2.2 (interior_subset ((hQ i).2.1 (mem_image_of_mem γ hs))))
    w hprimitive
  have hmin : reducedLength K.flow 0 p (γ (Real.sqrt tau)) tau ≤
      K.spatialReducedLengthInfimum p tau := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * Real.sqrt tau by positivity)).mp
    simpa only [hγ0] using hle.trans hbound
  exact ⟨γ (Real.sqrt tau), le_antisymm hmin (K.spatialReducedLengthInfimum_le p _ tau)⟩


theorem exists_reducedLength_minimizer (K : AncientKappaSolution 2 M)
    (p : M) {tau : ℝ} (htau : 0 < tau) :
    ∃ q : M, ∀ y : M, reducedLength K.flow 0 p q tau ≤ reducedLength K.flow 0 p y tau := by
  obtain ⟨q, hq⟩ := K.exists_reducedLength_eq_spatialInfimum p htau
  exact ⟨q, fun y => hq.le.trans (K.spatialReducedLengthInfimum_le p y tau)⟩

end PoincareConjecture.AncientKappaSolution
