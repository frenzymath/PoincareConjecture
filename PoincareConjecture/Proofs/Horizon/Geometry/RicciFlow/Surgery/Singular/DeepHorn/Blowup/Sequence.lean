import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.Levels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Blowup.Controlled.Geometry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.DeepHorn

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
  (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
  (Q : ∀ k, SingularLimitConclusion (H k))
  (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
  (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
  (hdiv : Filter.Tendsto (fun k =>
    ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
    Filter.atTop Filter.atTop)

def terminalBlowupSequence : GeneralizedBlowupSequence.{u} where
  flow k := (Q k).extension.extended
  base k := ⟨T k, x k⟩
  base_scalar_pos := hpos
  scalar_diverges := hdiv

theorem terminalBlowupSequence_balls_compact
    (hbounded : GeneralizedBlowupBoundedDistance (terminalBlowupSequence H Q x hpos hdiv)) :
    BlowupBaseBallsCompact (terminalBlowupSequence H Q x hpos hdiv) := by
  intro A hA
  obtain ⟨D, _, hD⟩ := hbounded A hA
  filter_upwards [hD] with k hk
  exact (Q k).isCompact_closure_of_scalar_bound _ _ hk

end PoincareConjecture.DeepHorn
