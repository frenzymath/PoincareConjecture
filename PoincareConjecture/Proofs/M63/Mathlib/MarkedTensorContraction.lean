import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture

structure MarkedTensorContraction (k : Nat) where
  order : Nat
  test : Fin (k + order)
  jet : Fin (k + order) -> Nat

namespace MarkedTensorContraction

def weight {k : Nat} (A : MarkedTensorContraction k) : Nat :=
  A.order + Finset.sum
    ((Finset.univ : Finset (Fin (k + A.order))).erase A.test) A.jet

def tensorStep {k : Nat} (A : MarkedTensorContraction k) :
    MarkedTensorContraction k :=
  { order := A.order + 1
    test := A.test.succ
    jet := Fin.cons 0 A.jet }

def slotStep {k : Nat} (A : MarkedTensorContraction k)
    (i : Fin (k + A.order)) : MarkedTensorContraction k :=
  { order := A.order
    test := A.test
    jet := Function.update A.jet i (A.jet i + 1) }

noncomputable def derivativeBranches {k : Nat}
    (A : MarkedTensorContraction k) : List (MarkedTensorContraction k) :=
  A.tensorStep ::
    (((Finset.univ : Finset (Fin (k + A.order))).erase A.test).toList.map
      A.slotStep)

end MarkedTensorContraction

noncomputable def markedTensorExpressionDerivative {k : Nat}
    (P : List (Int × MarkedTensorContraction k)) :
    List (Int × MarkedTensorContraction k) :=
  P.flatMap (fun q => q.2.derivativeBranches.map (fun A => (q.1, A)))

def markedTensorCoefficientMass {k : Nat}
    (P : List (Int × MarkedTensorContraction k)) : Nat :=
  (P.map (fun q => q.1.natAbs)).sum

theorem MarkedTensorContraction.derivativeBranches_spec
    {k : Nat} (A : MarkedTensorContraction k) :
    A.derivativeBranches.length = k + A.order ∧
      ∀ B ∈ A.derivativeBranches,
        B.weight = A.weight + 1 ∧
        A.order ≤ B.order ∧ B.order ≤ A.order + 1 := by
  classical
  have htensor : A.tensorStep.weight = A.weight + 1 := by
    have hold := Finset.sum_erase_add Finset.univ A.jet
      (Finset.mem_univ A.test)
    have hnew := Finset.sum_erase_add Finset.univ (Fin.cons 0 A.jet)
      (Finset.mem_univ A.test.succ)
    rw [Fin.sum_univ_succ] at hnew
    simp only [Fin.cons_zero, Fin.cons_succ, zero_add] at hnew
    have hsum :
        Finset.sum (Finset.univ.erase A.test.succ) (Fin.cons 0 A.jet) =
          Finset.sum (Finset.univ.erase A.test) A.jet :=
      Nat.add_right_cancel (hnew.trans hold.symm)
    change A.order + 1 +
        Finset.sum (Finset.univ.erase A.test.succ) (Fin.cons 0 A.jet) =
      A.order + Finset.sum (Finset.univ.erase A.test) A.jet + 1
    rw [hsum]
    omega
  have hslot (i : Fin (k + A.order)) (hi : i ∈ Finset.univ.erase A.test) :
      (A.slotStep i).weight = A.weight + 1 := by
    let s := (Finset.univ : Finset (Fin (k + A.order))).erase A.test
    have hold := Finset.sum_erase_add s A.jet hi
    have hnew := Finset.sum_erase_add s (Function.update A.jet i (A.jet i + 1)) hi
    have hsame :
        Finset.sum (s.erase i) (Function.update A.jet i (A.jet i + 1)) =
          Finset.sum (s.erase i) A.jet := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
    rw [hsame] at hnew
    simp only [Function.update_self] at hnew
    have hsum : Finset.sum s (Function.update A.jet i (A.jet i + 1)) =
        Finset.sum s A.jet + 1 := by
      calc
        _ = Finset.sum (s.erase i) A.jet + (A.jet i + 1) := hnew.symm
        _ = (Finset.sum (s.erase i) A.jet + A.jet i) + 1 :=
          (Nat.add_assoc _ _ _).symm
        _ = Finset.sum s A.jet + 1 := congrArg (fun n => n + 1) hold
    change A.order + Finset.sum s (Function.update A.jet i (A.jet i + 1)) =
      A.order + Finset.sum s A.jet + 1
    rw [hsum]
    omega
  constructor
  · have hpositive := A.test.isLt
    simp only [derivativeBranches, List.length_cons, List.length_map,
      Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ A.test),
      Finset.card_univ, Fintype.card_fin]
    omega
  · intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ⟨htensor, Nat.le_succ _, le_rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hB
      exact ⟨hslot i (Finset.mem_toList.mp hi), le_rfl, Nat.le_succ _⟩

theorem markedTensorExpressionDerivative_spec
    {k : Nat} (P : List (Int × MarkedTensorContraction k))
    {w d N : Nat}
    (hweight : ∀ q ∈ P, q.2.weight = w)
    (horder : ∀ q ∈ P, q.2.order ≤ d)
    (hrank : ∀ q ∈ P, k + q.2.order ≤ N) :
    (∀ q ∈ markedTensorExpressionDerivative P,
      q.2.weight = w + 1 ∧ q.2.order ≤ d + 1) ∧
    markedTensorCoefficientMass (markedTensorExpressionDerivative P) =
      (P.map (fun q => q.1.natAbs * (k + q.2.order))).sum ∧
    markedTensorCoefficientMass (markedTensorExpressionDerivative P) ≤
      N * markedTensorCoefficientMass P := by
  classical
  have hrepeat (z : Int) (L : List (MarkedTensorContraction k)) :
      markedTensorCoefficientMass (L.map (fun A => (z, A))) = z.natAbs * L.length := by
    induction L with
    | nil => simp [markedTensorCoefficientMass]
    | cons A L ih =>
      change z.natAbs + markedTensorCoefficientMass (L.map (fun B => (z, B))) =
        z.natAbs * (L.length + 1)
      rw [ih, Nat.mul_add, Nat.mul_one]
      exact Nat.add_comm _ _
  have happend (L Q : List (Int × MarkedTensorContraction k)) :
      markedTensorCoefficientMass (L ++ Q) =
        markedTensorCoefficientMass L + markedTensorCoefficientMass Q := by
    simp only [markedTensorCoefficientMass, List.map_append, List.sum_append]
  have hmass (Q : List (Int × MarkedTensorContraction k)) :
      markedTensorCoefficientMass (markedTensorExpressionDerivative Q) =
        (Q.map (fun q => q.1.natAbs * (k + q.2.order))).sum := by
    induction Q with
    | nil => rfl
    | cons q Q ih =>
      change markedTensorCoefficientMass
        (q.2.derivativeBranches.map (fun A => (q.1, A)) ++
          markedTensorExpressionDerivative Q) = _
      rw [happend, hrepeat, q.2.derivativeBranches_spec.1, ih]
      rfl
  have hbound (Q : List (Int × MarkedTensorContraction k))
      (hQrank : ∀ q ∈ Q, k + q.2.order ≤ N) :
      (Q.map (fun q => q.1.natAbs * (k + q.2.order))).sum ≤
        N * markedTensorCoefficientMass Q := by
    induction Q with
    | nil => simp [markedTensorCoefficientMass]
    | cons q Q ih =>
      have hq : q.1.natAbs * (k + q.2.order) ≤ N * q.1.natAbs := by
        simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_left q.1.natAbs (hQrank q (List.mem_cons_self))
      have htail := ih (fun r hr => hQrank r (List.mem_cons_of_mem q hr))
      simpa only [markedTensorCoefficientMass, List.map_cons, List.sum_cons,
        Nat.mul_add] using Nat.add_le_add hq htail
  refine ⟨?_, hmass P, (hmass P).trans_le (hbound P hrank)⟩
  intro q hq
  obtain ⟨r, hr, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hq
  have hspec := r.2.derivativeBranches_spec.2 A hA
  exact ⟨hspec.1.trans (congrArg (fun v => v + 1) (hweight r hr)),
    hspec.2.2.trans (Nat.add_le_add_right (horder r hr) 1)⟩

end PoincareConjecture
