import PoincareConjecture.Definitions.M46NoncollapseInduction
import PoincareConjecture.Definitions.M15Noncollapsing








set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46



noncomputable def actionBudget {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : ℝ :=
  8 * Real.sqrt (surgeryEpochStart (p.i + 1)) * (1 + surgeryEpochStart (p.i + 1))



noncomputable def configurationKappa {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) : ℝ :=
  min (p.kappa (Fin.last p.i)) (min (p.kappa 0) (U.kappa / 8))


theorem configurationKappa_pos {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) :
    0 < configurationKappa p U :=
  lt_min (p.kappa_pos _) (lt_min (p.kappa_pos _) (div_pos U.kappa_pos (by norm_num)))


theorem configurationKappa_le_last {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) :
    configurationKappa p U ≤ p.kappa (Fin.last p.i) := min_le_left _ _


theorem configurationKappa_le_seed {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) :
    configurationKappa p U ≤ p.kappa 0 :=
  (min_le_right _ _).trans (min_le_left _ _)


theorem configurationKappa_le_uniform {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V) :
    configurationKappa p U ≤ U.kappa / 8 :=
  (min_le_right _ _).trans (min_le_right _ _)

end PoincareConjecture.Proofs.M46
