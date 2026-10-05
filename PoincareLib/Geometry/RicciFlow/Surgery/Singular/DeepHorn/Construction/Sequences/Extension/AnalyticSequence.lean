import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.Extension.AnalyticTime
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.Sequence

/-!
# M30's guarded analytic estimates for terminal blowup sequences

Morgan--Tian Claim 11.32, printed pp. 287-288, uses the common original
analytic constant above four times each blowup scale. A strict separation
from the old canonical cutoff lets the extension estimates apply at all
included times, including zero and the terminal endpoint.

The donors are `DeepHorn.terminalBlowupSequence_scalar_gradient_bound` and
`DeepHorn.terminalBlowupSequence_scalar_time_derivative_bound` in Horizon
`Surgery/Singular/DeepHorn/Blowup/Controls.lean`. The actual extensions and
original clocks are retained, and the M04 theory is supplied explicitly.
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

/-- The sequence satisfies M30's gradient guard with its common analytic
coefficient, including terminal times; Claim 11.32, printed pp. 287-288. -/
theorem terminalBlowupSequence_scalar_gradient_bound
    (hM04 : RicciFlowCurvatureTheory.{u}) {B : ℝ}
    (hB : ∀ k, (H k).analytic_constant = B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k)
    (k : ℕ) (t : ℝ) (ht : t ∈ (Q k).extension.extended.interval)
    (y : ((Q k).extension.extended.slice t).carrier)
    (hy : 4 * (terminalBlowupSequence H Q x hpos hdiv).scale k ≤
      ((Q k).extension.extended.connection t).scalarCurvature y)
    (v : TangentSpace (𝓡 3) y)
    (hv : ((Q k).extension.extended.metric t).inner y v v = 1) :
    |mvfderiv (𝓡 3) ((Q k).extension.extended.connection t).scalarCurvature y v| ≤
      B * ((Q k).extension.extended.connection t).scalarCurvature y ^ (3 / 2 : ℝ) := by
  simpa only [hB k] using extension_scalar_gradient_bound_of_strict
    hM04 (H k) (Q k).extension t ht y ((hcutoff k).trans_le hy) v hv

/-- The sequence satisfies M30's absolute within-box derivative guard at
all included times, as used in Claim 11.32, printed pp. 287-288. -/
theorem terminalBlowupSequence_scalar_time_derivative_bound
    (hM04 : RicciFlowCurvatureTheory.{u}) {B : ℝ}
    (hB : ∀ k, (H k).analytic_constant = B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k)
    (k : ℕ) (b : (Q k).extension.extended.box_index) (t : ℝ)
    (ht : t ∈ ((Q k).extension.extended.box b).interval)
    (y : ((Q k).extension.extended.box b).carrier.carrier)
    (hy : 4 * (terminalBlowupSequence H Q x hpos hdiv).scale k ≤
      (((Q k).extension.extended.box b).flow.connection t).scalarCurvature y) :
    ∃ d : ℝ, HasDerivWithinAt
      (fun s => (((Q k).extension.extended.box b).flow.connection s).scalarCurvature y) d
      ((Q k).extension.extended.box b).interval t ∧
      |d| ≤ B * (((Q k).extension.extended.box b).flow.connection t).scalarCurvature y ^ 2 := by
  simpa only [hB k] using extension_scalar_time_derivative_bound
    hM04 (H k) (Q k).extension b t ht y ((hcutoff k).trans_le hy)

end PoincareMT.M32
