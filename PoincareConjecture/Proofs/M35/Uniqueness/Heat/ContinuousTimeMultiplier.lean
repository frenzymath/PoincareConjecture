import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeDependentOperator
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Order.ProjIcc









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped BoundedContinuousFunction

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def continuousTimeAction (μ : Measure ℝ) (A : ℝ →ᵇ (E →L[ℝ] F)) :
    Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  timeDependentLpOperator A.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => A.norm_coe_le_norm t))

theorem continuousTimeAction_coe (μ : Measure ℝ) (A : ℝ →ᵇ (E →L[ℝ] F)) (u : Lp E 2 μ) :
    continuousTimeAction μ A u =ᵐ[μ] fun t => A t (u t) :=
  timeDependentLpOperator_coe _ _ u

theorem norm_continuousTimeAction_le (μ : Measure ℝ) (A : ℝ →ᵇ (E →L[ℝ] F)) :
    ‖continuousTimeAction μ A‖ ≤ ‖A‖ :=
  norm_timeDependentLpOperator_le _ _ (norm_nonneg A)

def continuousTimeActionLinear (μ : Measure ℝ) :
    (ℝ →ᵇ (E →L[ℝ] F)) →ₗ[ℝ] (Lp E 2 μ →L[ℝ] Lp F 2 μ) where
  toFun := continuousTimeAction μ
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [continuousTimeAction_coe μ (A + B) u,
      continuousTimeAction_coe μ A u, continuousTimeAction_coe μ B u,
      Lp.coeFn_add (continuousTimeAction μ A u) (continuousTimeAction μ B u)]
      with t hab ha hb hs
    change (continuousTimeAction μ (A + B) u) t =
      (continuousTimeAction μ A u + continuousTimeAction μ B u) t
    rw [hab, hs, Pi.add_apply, ha, hb]
    rfl
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [continuousTimeAction_coe μ (c • A) u,
      continuousTimeAction_coe μ A u, Lp.coeFn_smul c (continuousTimeAction μ A u)]
      with t hca ha hs
    change (continuousTimeAction μ (c • A) u) t = (c • continuousTimeAction μ A u) t
    rw [hca, hs, Pi.smul_apply, ha]
    rfl

def continuousTimeLp (μ : Measure ℝ) :
    (ℝ →ᵇ (E →L[ℝ] F)) →L[ℝ] (Lp E 2 μ →L[ℝ] Lp F 2 μ) :=
  (continuousTimeActionLinear (E := E) (F := F) μ).mkContinuous 1 (by
    intro A
    change ‖continuousTimeAction μ A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using norm_continuousTimeAction_le μ A)

theorem continuousTimeLp_coe (μ : Measure ℝ) (A : ℝ →ᵇ (E →L[ℝ] F)) (u : Lp E 2 μ) :
    continuousTimeLp μ A u =ᵐ[μ] fun t => A t (u t) :=
  continuousTimeAction_coe μ A u

theorem norm_continuousTimeLp_le (μ : Measure ℝ) :
    ‖continuousTimeLp (E := E) (F := F) μ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖continuousTimeAction μ A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using norm_continuousTimeAction_le μ A

end PoincareConjecture.M35.Uniqueness.Heat
