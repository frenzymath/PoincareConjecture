import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

open Filter Function MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace PoincareConjecture

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

structure BanachVolterraProblem where
  T : ℝ
  T_nonneg : 0 ≤ T
  initial : E
  source : ℝ → E → E
  radius : NNReal
  sourceLipschitz : NNReal
  sourceBound : NNReal
  source_lipschitzOn :
    ∀ t ∈ Icc (0 : ℝ) T,
      LipschitzOnWith sourceLipschitz (source t)
        (Metric.closedBall initial radius)
  source_continuousOn :
    ∀ x ∈ Metric.closedBall initial radius,
      ContinuousOn (source · x) (Icc (0 : ℝ) T)
  source_norm_le :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Metric.closedBall initial radius,
      ‖source t x‖ ≤ sourceBound
  small_time : (sourceBound : ℝ) * T ≤ (radius : ℝ)

namespace BanachVolterraProblem

variable (P : BanachVolterraProblem (E := E))

def initialTime : Icc (0 : ℝ) P.T :=
  ⟨0, le_rfl, P.T_nonneg⟩

@[simp] theorem initialTime_val : (P.initialTime : ℝ) = 0 := rfl

theorem toPicardLindelof :
    IsPicardLindelof P.source P.initialTime P.initial P.radius 0
      P.sourceBound P.sourceLipschitz := by
  refine { lipschitzOnWith := ?_, continuousOn := ?_, norm_le := ?_, mul_max_le := ?_ }
  · intro t ht
    exact P.source_lipschitzOn t ht
  · intro x hx
    exact P.source_continuousOn x hx
  · intro t ht x hx
    exact P.source_norm_le t ht x hx
  · simpa [initialTime, max_eq_left P.T_nonneg] using P.small_time

theorem initial_mem_closedBall :
    P.initial ∈ Metric.closedBall P.initial ((0 : NNReal) : ℝ) := by
  exact Metric.mem_closedBall_self (by norm_num)

noncomputable def fixedPoint :
    ODE.FunSpace P.initialTime P.initial 0 P.sourceBound :=
  Classical.choose
    (ODE.FunSpace.exists_isFixedPt_next P.toPicardLindelof
      P.initial_mem_closedBall)

theorem fixedPoint_isFixedPt :
    Function.IsFixedPt
      (ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall)
      P.fixedPoint := by
  exact Classical.choose_spec
    (ODE.FunSpace.exists_isFixedPt_next P.toPicardLindelof
      P.initial_mem_closedBall)

noncomputable def solution : ℝ → E := P.fixedPoint.compProj

theorem solution_eq_fixedPoint (t : Icc (0 : ℝ) P.T) :
    P.solution (t : ℝ) = P.fixedPoint t := by
  exact P.fixedPoint.compProj_val

theorem solution_initial_trace : P.solution 0 = P.initial := by
  have hfix := P.fixedPoint_isFixedPt
  have hval := congrArg
    (fun α : ODE.FunSpace P.initialTime P.initial 0 P.sourceBound =>
      α P.initialTime) hfix
  calc
    P.solution 0 = P.fixedPoint P.initialTime := by
      change P.fixedPoint.compProj (P.initialTime : ℝ) =
        P.fixedPoint P.initialTime
      exact P.fixedPoint.compProj_val
    _ = (ODE.FunSpace.next P.toPicardLindelof
      P.initial_mem_closedBall P.fixedPoint) P.initialTime := hval.symm
    _ = P.initial := by
      exact ODE.FunSpace.next_apply₀ P.toPicardLindelof
        P.initial_mem_closedBall P.fixedPoint

theorem solution_integral_equation {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.T) :
    P.solution t = P.initial +
      ∫ s in (0 : ℝ)..t, P.source s (P.solution s) := by
  rw [P.solution_eq_fixedPoint ⟨t, ht⟩]
  have hiff :=
    (ODE.FunSpace.isFixedPt_next_iff P.toPicardLindelof
      P.initial_mem_closedBall).1 P.fixedPoint_isFixedPt
  have h := hiff ⟨t, ht⟩
  simpa [ODE.picard_apply, solution] using h

theorem solution_hasDerivWithinAt {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.T) :
    HasDerivWithinAt P.solution
      (P.source t (P.solution t)) (Icc (0 : ℝ) P.T) t := by
  apply ODE.hasDerivWithinAt_picard_Icc
      P.initialTime.2 P.toPicardLindelof.continuousOn_uncurry
      P.fixedPoint.continuous_compProj.continuousOn
      (fun _ ht' => P.fixedPoint.compProj_mem_closedBall (a := P.radius)
        P.toPicardLindelof.mul_max_le)
      P.initial ht |>.congr_of_mem _ ht
  intro t' ht'
  calc
    P.solution t' = P.fixedPoint ⟨t', ht'⟩ := by
      change P.fixedPoint.compProj t' = P.fixedPoint ⟨t', ht'⟩
      exact P.fixedPoint.compProj_of_mem ht'
    _ = (ODE.FunSpace.next P.toPicardLindelof
        P.initial_mem_closedBall P.fixedPoint) ⟨t', ht'⟩ := by
      exact congrArg
        (fun α : ODE.FunSpace P.initialTime P.initial 0 P.sourceBound =>
          α ⟨t', ht'⟩) P.fixedPoint_isFixedPt.symm
    _ = ODE.picard P.source (P.initialTime : ℝ) P.initial
        P.fixedPoint.compProj t' := by
      rw [ODE.FunSpace.next_apply]

theorem continuous_solution : Continuous P.solution :=
  P.fixedPoint.continuous_compProj

end BanachVolterraProblem

end

end PoincareConjecture
