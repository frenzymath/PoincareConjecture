import PoincareConjecture.Proofs.M32.Claim11_32.Compactness
import PoincareConjecture.Statements.M29GeneralizedDistance
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

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
  (hdiv : Tendsto (fun k =>
    ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)

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
  exact terminalClosure_isCompact_of_scalarBound (Q k) _ _ hk

theorem terminalBlowupSequence_boundedDistance_and_compact
    (hM29 : RepairedGeneralizedBoundedDistanceTheory.{u})
    {epsilon C : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_small : epsilon ≤ Classical.choose hM29.constants) (hC_pos : 0 < C)
    (hcontrols : GeneralizedBoundedDistanceHypotheses
      (terminalBlowupSequence H Q x hpos hdiv) epsilon C) :
    GeneralizedBlowupBoundedDistance (terminalBlowupSequence H Q x hpos hdiv) ∧
      BlowupBaseBallsCompact (terminalBlowupSequence H Q x hpos hdiv) := by
  have hb := (Classical.choose_spec hM29.constants).2.2 epsilon
    hepsilon_pos hepsilon_small C hC_pos (terminalBlowupSequence H Q x hpos hdiv) hcontrols
  exact ⟨hb, terminalBlowupSequence_balls_compact H Q x hpos hdiv hb⟩

theorem terminalBlowupSequence_eventually_cutoff (r₀ : ℝ)
    (hradius : ∀ k, (H k).r₀ = r₀) :
    ∀ᶠ k : ℕ in atTop, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k := by
  filter_upwards [hdiv.eventually (eventually_gt_atTop (r₀⁻¹ ^ 2 / 4))] with k hk
  rw [hradius k]
  change r₀⁻¹ ^ 2 < 4 * ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)
  linarith

end PoincareConjecture.M32
