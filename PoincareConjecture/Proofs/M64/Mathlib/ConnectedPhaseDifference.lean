import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularAngles
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

open Proofs.M58

private theorem angularPoint_eq_iff_exp_eq {s t : ℝ} :
    angularPoint s = angularPoint t ↔ Circle.exp s = Circle.exp t := by
  rw [← m60LoopCircleHomeomorphCircle_angular s,
    ← m60LoopCircleHomeomorphCircle_angular t,
    m60LoopCircleHomeomorphCircle.injective.eq_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem m64ContinuousPhase_difference {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsPreconnected S) {u v : X → ℝ} {k : ℝ} (hk : k ≠ 0)
    (hu : ContinuousOn u S) (hv : ContinuousOn v S)
    (hobs : ∀ x ∈ S, angularPoint (k * u x) = angularPoint (k * v x))
    {a : X} (ha : a ∈ S) :
    ∀ x ∈ S, u x = v x + (u a - v a) := by
  have hzero (x : X) (hx : x ∈ S) : Circle.exp (k * (u x - v x)) = 1 := by
    rw [mul_sub, Circle.exp_sub, (angularPoint_eq_iff_exp_eq.mp (hobs x hx)), div_self']
  have heq := Circle.isCoveringMap_exp.eqOn_of_comp_eqOn hS
    (continuousOn_const.mul (hu.sub hv)) continuousOn_const
    (show EqOn (Circle.exp ∘ fun x => k * (u x - v x))
      (Circle.exp ∘ fun _ => k * (u a - v a)) S from
        fun x hx => (hzero x hx).trans (hzero a ha).symm) ha rfl
  intro x hx
  have h := mul_left_cancel₀ hk (heq hx)
  change u x - v x = u a - v a at h
  linarith

theorem m64AngularPoint_phase_shift {k u v : ℝ}
    (hobs : angularPoint (k * u) = angularPoint (k * v)) (t : ℝ) :
    angularPoint (k * (t + (u - v))) = angularPoint (k * t) := by
  apply angularPoint_eq_iff_exp_eq.mpr
  rw [mul_add, mul_sub, Circle.exp_add, Circle.exp_sub,
    angularPoint_eq_iff_exp_eq.mp hobs, div_self', mul_one]

end PoincareConjecture
