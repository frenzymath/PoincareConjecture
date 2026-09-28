import Mathlib
import PoincareConjecture.Proofs.M05.Analysis.ODE.Endpoint

namespace Poincare.HamiltonIvey

open Set
open scoped BigOperators

noncomputable section

abbrev ThreeMatrix := Matrix (Fin 3) (Fin 3) ℝ

local instance : NormedAddCommGroup ThreeMatrix := Matrix.normedAddCommGroup
local instance : NormedSpace ℝ ThreeMatrix := Matrix.normedSpace

def operatorReaction (A : ThreeMatrix) : ThreeMatrix :=
  2 • (A * A + Matrix.adjugate A)

theorem operatorReaction_eq_trace_polynomial (A : ThreeMatrix) :
    operatorReaction A =
      (4 : ℝ) • (A * A) - (2 * A.trace) • A +
        (A.trace ^ 2 - (A * A).trace) • (1 : ThreeMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorReaction, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_succ] <;> ring

theorem operatorReaction_diagonal_entries (d : Fin 3 → ℝ) :
    operatorReaction (Matrix.diagonal d) = Matrix.diagonal
      ![2 * (d 0 ^ 2 + d 1 * d 2), 2 * (d 1 ^ 2 + d 0 * d 2),
        2 * (d 2 ^ 2 + d 0 * d 1)] := by
  rw [operatorReaction_eq_trace_polynomial]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Fin.sum_univ_succ] <;> ring

private def reflect (k : Fin 3) (A : ThreeMatrix) : ThreeMatrix :=
  fun i j => (if i = k then -1 else 1) * A i j * (if j = k then -1 else 1)

private theorem reflect_reaction (k : Fin 3) (A : ThreeMatrix) :
    reflect k (operatorReaction A) = operatorReaction (reflect k A) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [reflect, operatorReaction, Matrix.adjugate_fin_three,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem contDiff_operatorReaction : ContDiff ℝ 1 operatorReaction := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [operatorReaction, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> fun_prop

private theorem reflect_continuous (k : Fin 3) : Continuous (reflect k) := by
  unfold reflect
  fun_prop

private theorem reflect_deriv (k : Fin 3) {A : ℝ → ThreeMatrix} {D : ThreeMatrix}
    {t : ℝ} (hA : HasDerivAt A D t) :
    HasDerivAt (fun s => reflect k (A s)) (reflect k D) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j).const_mul _).mul_const _

theorem operator_reaction_stays_diagonal
    {a b : ℝ} {A : ℝ → ThreeMatrix}
    (hA : ContinuousOn A (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt A (operatorReaction (A t)) t)
    (hinit : ∀ i j, i ≠ j → A a i j = 0) :
    ∀ t ∈ Icc a b, ∀ i j, i ≠ j → A t i j = 0 := by
  have hdright := Poincare.hasDerivWithinAt_Ici_of_continuousOn hA
    (contDiff_operatorReaction.continuous.comp_continuousOn hA) hd
  have hreflect (k : Fin 3) : EqOn (fun t => reflect k (A t)) A (Icc a b) := by
    have hRc := (reflect_continuous k).comp_continuousOn hA
    have hRd := Poincare.hasDerivWithinAt_Ici_of_continuousOn hRc
      (contDiff_operatorReaction.continuous.comp_continuousOn hRc)
      (fun t ht => show HasDerivAt (reflect k ∘ A)
        (operatorReaction (reflect k (A t))) t from by
          simpa only [Function.comp_def, reflect_reaction] using reflect_deriv k (hd t ht))
    let S := A '' Icc a b ∪ (fun t => reflect k (A t)) '' Icc a b
    have hS : IsCompact S :=
      (isCompact_Icc.image_of_continuousOn hA).union
        (isCompact_Icc.image_of_continuousOn ((reflect_continuous k).comp_continuousOn hA))
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
      contDiff_operatorReaction.locallyLipschitz.locallyLipschitzOn
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => operatorReaction) (s := fun _ => S) (fun _ _ => hK)
      ((reflect_continuous k).comp_continuousOn hA)
      hRd (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩)
      hA hdright
      (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
    · ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : i = k <;> simp [reflect, hi]
      · simp [reflect, hinit i j hij]
  intro t ht i j hij
  have h := congrFun (congrFun (hreflect i ht) i) j
  simp [reflect, hij.symm] at h
  linarith

end

end Poincare.HamiltonIvey
