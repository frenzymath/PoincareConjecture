import PoincareConjecture.Proofs.M63.Mathlib.MarkedTensorContraction
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum










set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture


noncomputable def m63RiemannJetErrorExpression :
    Nat -> List (Int × MarkedTensorContraction 4)
  | 0 => [(1, { order := 0, test := 2, jet := ![1, 0, 0, 0] })]
  | m + 1 =>
      markedTensorExpressionDerivative (m63RiemannJetErrorExpression m) ++
        [(1, { order := 0, test := 2, jet := ![1, 0, 0, m + 1] })]


noncomputable def m63RicciJetErrorExpression :
    Nat -> List (Int × MarkedTensorContraction 2)
  | 0 =>
      [(-2, { order := 1, test := 2, jet := ![0, 0, 0] }),
       (1, { order := 1, test := 0, jet := ![0, 0, 0] })]
  | m + 1 =>
      markedTensorExpressionDerivative (m63RicciJetErrorExpression m) ++
        [(-1, { order := 1, test := 2, jet := ![0, m + 1, 0] }),
         (-1, { order := 1, test := 2, jet := ![m + 1, 0, 0] }),
         (1, { order := 1, test := 0, jet := ![0, 0, m + 1] })]


def m63JetErrorMassBound : Nat -> Nat
  | 0 => 4
  | m + 1 => (m + 4) * m63JetErrorMassBound m + 4




theorem m63JetErrorExpression_spec (m : Nat) :
    (∀ q ∈ m63RiemannJetErrorExpression m,
      q.2.weight = m + 1 ∧ q.2.order ≤ m) ∧
    (∀ q ∈ m63RicciJetErrorExpression m,
      q.2.weight = m + 1 ∧ q.2.order ≤ m + 1) ∧
    markedTensorCoefficientMass (m63RiemannJetErrorExpression m) +
      markedTensorCoefficientMass (m63RicciJetErrorExpression m) ≤
        m63JetErrorMassBound m := by
  classical
  have hw {k : Nat} (A : MarkedTensorContraction k) :
      A.weight + A.jet A.test = A.order + ∑ i, A.jet i := by
    dsimp only [MarkedTensorContraction.weight]
    rw [Nat.add_assoc, Finset.sum_erase_add _ _ (Finset.mem_univ A.test)]
  have hR (m : Nat) :
      (⟨0, 2, ![1, 0, 0, m + 1]⟩ : MarkedTensorContraction 4).weight = m + 2 := by
    have h := hw (⟨0, 2, ![1, 0, 0, m + 1]⟩ : MarkedTensorContraction 4)
    simp [Fin.sum_univ_succ] at h
    omega
  have hA (m : Nat) :
      (⟨1, 2, ![0, m + 1, 0]⟩ : MarkedTensorContraction 2).weight = m + 2 := by
    have h := hw (⟨1, 2, ![0, m + 1, 0]⟩ : MarkedTensorContraction 2)
    simp [Fin.sum_univ_succ] at h
    omega
  have hB (m : Nat) :
      (⟨1, 2, ![m + 1, 0, 0]⟩ : MarkedTensorContraction 2).weight = m + 2 := by
    have h := hw (⟨1, 2, ![m + 1, 0, 0]⟩ : MarkedTensorContraction 2)
    simp [Fin.sum_univ_succ] at h
    omega
  have hC (m : Nat) :
      (⟨1, 0, ![0, 0, m + 1]⟩ : MarkedTensorContraction 2).weight = m + 2 := by
    have h := hw (⟨1, 0, ![0, 0, m + 1]⟩ : MarkedTensorContraction 2)
    simp [Fin.sum_univ_succ] at h
    omega
  induction m with
  | zero =>
    constructor
    · intro q hq
      simp only [m63RiemannJetErrorExpression, List.mem_singleton] at hq
      subst q
      exact ⟨by decide, by decide⟩
    constructor
    · intro q hq
      simp only [m63RicciJetErrorExpression, List.mem_cons, List.mem_nil_iff,
        or_false] at hq
      rcases hq with rfl | rfl <;> exact ⟨by decide, by decide⟩
    · norm_num [m63RiemannJetErrorExpression, m63RicciJetErrorExpression,
        markedTensorCoefficientMass, m63JetErrorMassBound]
  | succ m ih =>
    have hRm := markedTensorExpressionDerivative_spec
      (m63RiemannJetErrorExpression m)
      (fun q hq => (ih.1 q hq).1) (fun q hq => (ih.1 q hq).2)
      (N := m + 4) (fun q hq => by have := (ih.1 q hq).2; omega)
    have hRic := markedTensorExpressionDerivative_spec
      (m63RicciJetErrorExpression m)
      (fun q hq => (ih.2.1 q hq).1) (fun q hq => (ih.2.1 q hq).2)
      (N := m + 4) (fun q hq => by have := (ih.2.1 q hq).2; omega)
    constructor
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · simpa only [Nat.add_assoc] using hRm.1 q hq
      · have hq := List.mem_singleton.mp hq
        subst q
        exact ⟨hR m, Nat.zero_le _⟩
    constructor
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · simpa only [Nat.add_assoc] using hRic.1 q hq
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact ⟨hA m, by change 1 ≤ m + 1 + 1; omega⟩
        · exact ⟨hB m, by change 1 ≤ m + 1 + 1; omega⟩
        · exact ⟨hC m, by change 1 ≤ m + 1 + 1; omega⟩
    · have hsum := Nat.add_le_add hRm.2.2 hRic.2.2
      have hbound := Nat.mul_le_mul_left (m + 4) ih.2.2
      rw [Nat.mul_add] at hbound
      simp only [m63RiemannJetErrorExpression, m63RicciJetErrorExpression,
        m63JetErrorMassBound, markedTensorCoefficientMass, List.map_append,
        List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      change _ + 1 + (_ + (1 + (1 + (1 + 0)))) ≤ _
      dsimp only [markedTensorCoefficientMass] at hsum hbound
      omega

end PoincareConjecture
