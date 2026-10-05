import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.Compactness
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.BoundsTheory
import Mathlib.Tactic.Linarith
open scoped PoincareMT.DeepHornSource

/-!
# Terminal blowup sequences and compact base balls

Morgan--Tian Claims 11.32-11.33, printed pp. 287-288, use a sequence of actual
terminal extensions whose base scalars tend to infinity. The frozen M29
service supplies bounded-distance curvature estimates once its primitive
pinching and canonical hypotheses have been established.

Donor declarations in Horizon `Surgery/Singular/DeepHorn/` are
`DeepHorn.terminalBlowupSequence` and
`DeepHorn.terminalBlowupSequence_balls_compact` in `Blowup/Sequence.lean`,
and `DeepHorn.terminalBlowupSequence_boundedDistance_and_compact` in
`Blowup/Controls.lean`. The M29 hypotheses remain explicit here; none of
these helpers replaces their geometric verification.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

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

/-- The actual terminal extensions with their original clocks and scalar
bases, as in Morgan--Tian Claim 11.32, printed pp. 287-288. -/
def terminalBlowupSequence : GeneralizedBlowupSequence.{u} where
  flow k := (Q k).extension.extended
  base k := ⟨T k, x k⟩
  base_scalar_pos := hpos
  scalar_diverges := hdiv

/-- M29's bounded-distance estimate and terminal properness give compact
closures of normalized base balls, as in Claim 11.33, printed p. 288. -/
theorem terminalBlowupSequence_balls_compact
    (hbounded : GeneralizedBlowupBoundedDistance (terminalBlowupSequence H Q x hpos hdiv)) :
    BlowupBaseBallsCompact (terminalBlowupSequence H Q x hpos hdiv) := by
  intro A hA
  obtain ⟨D, _, hD⟩ := hbounded A hA
  filter_upwards [hD] with k hk
  exact terminalClosure_isCompact_of_scalarBound (Q k) _ _ hk

/-- The frozen M29 service yields curvature bounds and compact base balls
under its explicit hypotheses, as used in Claims 11.32-11.33, pp. 287-288. -/
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

/-- Divergence of the base scalars eventually dominates a common canonical
cutoff, the first reduction in Claim 11.32, printed p. 288. -/
theorem terminalBlowupSequence_eventually_cutoff (r₀ : ℝ)
    (hradius : ∀ k, (H k).r₀ = r₀) :
    ∀ᶠ k : ℕ in atTop, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k := by
  filter_upwards [hdiv.eventually (eventually_gt_atTop (r₀⁻¹ ^ 2 / 4))] with k hk
  rw [hradius k]
  change r₀⁻¹ ^ 2 < 4 * ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)
  linarith

end PoincareMT.M32
