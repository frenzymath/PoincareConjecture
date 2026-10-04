import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseData
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Provider

/-!
# The old-prefix constants in Proposition 16.1

Morgan--Tian, pp. 367-368 and 391-394. These choices precede the new
surgery radius and every observed flow.
-/

set_option autoImplicit false
-- Preserve the native and retained-slice tangent instances in these data.
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.Proofs.M46

/-- The fixed action budget used on pp. 393-394. It depends only on the
old prefix. Comparison paths have a factor-two margin below this budget. -/
noncomputable def actionBudget {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : ℝ :=
  8 * Real.sqrt (surgeryEpochStart (p.i + 1)) * (1 + surgeryEpochStart (p.i + 1))

/-- Proposition 16.1's constant is fixed before the next radius and the flow.
The factor eight is the half-radius loss in the Theorem 8.1 application. -/
noncomputable def configurationKappa {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) : ℝ :=
  min (p.kappa (Fin.last p.i)) (min (p.kappa 0) (U.kappa / 8))

/-- Positivity of the common constant in Proposition 16.1, p. 367. -/
theorem configurationKappa_pos {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) :
    0 < configurationKappa p U :=
  lt_min (p.kappa_pos _) (lt_min (p.kappa_pos _) (div_pos U.kappa_pos (by norm_num)))

/-- The new constant is at most the old final constant, Proposition 16.1. -/
theorem configurationKappa_le_last {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) :
    configurationKappa p U ≤ p.kappa (Fin.last p.i) := min_le_left _ _

/-- The common constant includes the initial seed, Remark 16.2, p. 368. -/
theorem configurationKappa_le_seed {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) :
    configurationKappa p U ≤ p.kappa 0 :=
  (min_le_right _ _).trans (min_le_left _ _)

/-- Theorem 8.1's half-radius constant dominates the chosen constant. -/
theorem configurationKappa_le_uniform {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) :
    configurationKappa p U ≤ U.kappa / 8 :=
  (min_le_right _ _).trans (min_le_right _ _)

end PoincareMT.Proofs.M46
