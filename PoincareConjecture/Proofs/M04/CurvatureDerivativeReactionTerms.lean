import PoincareConjecture.Proofs.M04.CurvatureDerivativeContractions
import PoincareConjecture.Proofs.M04.CurvatureDerivativeEvolution
import PoincareConjecture.Proofs.M04.ScalarContractions
import PoincareConjecture.Definitions.Ch03.CurvatureReaction
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FinCases









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

structure ReactionTerm (m : ℕ) where
  leftOrder : ℕ
  rightOrder : ℕ
  orders_eq : leftOrder + rightOrder = m
  negative : Bool
  slots : (Fin (4 + leftOrder) ⊕ Fin (4 + rightOrder)) ≃ Fin ((4 + m) + 4)

noncomputable def reactionTermEvaluation (D : LeviCivitaData g)
    {m : ℕ} (T : ReactionTerm m) : CovariantTensorEvaluation n M (4 + m) :=
  fun x v ↦ if T.negative = true then
    -(curvaturePairContraction D T.leftOrder T.rightOrder T.slots x v)
  else curvaturePairContraction D T.leftOrder T.rightOrder T.slots x v

noncomputable def reactionListEvaluation (D : LeviCivitaData g)
    {m : ℕ} (L : List (ReactionTerm m)) : CovariantTensorEvaluation n M (4 + m) :=
  fun x v ↦ (L.map (fun T ↦ reactionTermEvaluation D T x v)).sum

private def correctionFiveEquiv (k : ℕ) :
    (Fin 5 ⊕ Fin k) ≃ Fin ((k + 1) + 4) :=
  let h4 : Fin 5 ≃ (Fin 4 ⊕ PUnit.{1}) :=
    (finSuccEquiv 4).trans (Equiv.optionEquivSumPUnit.{0, 0} (Fin 4))
  let hk : Fin (k + 1) ≃ (Fin k ⊕ PUnit.{1}) :=
    (finSuccEquiv k).trans (Equiv.optionEquivSumPUnit.{0, 0} (Fin k))
  (h4.sumCongr (Equiv.refl (Fin k))).trans <|
    (Equiv.sumAssoc (Fin 4) PUnit.{1} (Fin k)).trans <|
      ((Equiv.refl (Fin 4)).sumCongr (Equiv.sumComm PUnit.{1} (Fin k))).trans <|
        (Equiv.sumComm (Fin 4) (Fin k ⊕ PUnit.{1})).trans <|
          (hk.symm.sumCongr (Equiv.refl (Fin 4))).trans finSumFinEquiv

private theorem correctionFiveEquiv_inl_zero (k : ℕ) :
    correctionFiveEquiv k (Sum.inl 0) = Fin.castAdd 4 (0 : Fin (k + 1)) := by
  simp [correctionFiveEquiv, Equiv.sumCongr]

private theorem correctionFiveEquiv_inl_succ (k : ℕ) (s : Fin 4) :
    correctionFiveEquiv k (Sum.inl s.succ) = Fin.natAdd (k + 1) s := by
  simp [correctionFiveEquiv, Equiv.sumCongr]

private theorem correctionFiveEquiv_inr (k : ℕ) (r : Fin k) :
    correctionFiveEquiv k (Sum.inr r) = Fin.castAdd 4 r.succ := by
  simp [correctionFiveEquiv, Equiv.sumCongr]

private def correctionFourEquiv (k : ℕ) :
    (Fin 4 ⊕ Fin (k + 1)) ≃ Fin ((k + 1) + 4) :=
  (Equiv.sumComm (Fin 4) (Fin (k + 1))).trans finSumFinEquiv

private theorem correctionFourEquiv_inl (k : ℕ) (s : Fin 4) :
    correctionFourEquiv k (Sum.inl s) = Fin.natAdd (k + 1) s := by
  rfl

private theorem correctionFourEquiv_inr (k : ℕ) (s : Fin (k + 1)) :
    correctionFourEquiv k (Sum.inr s) = Fin.castAdd 4 s := by
  rfl

private def baseRowMap : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 4, 1, 6, 2, 5, 3, 7], ![0, 4, 1, 6, 3, 5, 2, 7],
    ![0, 4, 3, 6, 1, 5, 2, 7], ![0, 4, 2, 6, 1, 5, 3, 7],
    ![0, 4, 6, 5, 7, 1, 2, 3], ![1, 4, 6, 5, 0, 7, 2, 3],
    ![2, 4, 6, 5, 0, 1, 7, 3], ![3, 4, 6, 5, 0, 1, 2, 7]]

private theorem baseRowMap_bijective (row : Fin 8) :
    Function.Bijective (baseRowMap row) := by
  fin_cases row <;> decide

private noncomputable def basePermutation (row : Fin 8) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (baseRowMap row) (baseRowMap_bijective row)

private def correctionFiveRowMap : Fin 4 → Fin 5 → Fin 5 :=
  ![![0, 4, 1, 3, 2], ![4, 0, 1, 3, 2],
    ![3, 0, 1, 4, 2], ![1, 0, 2, 3, 4]]

private theorem correctionFiveRowMap_bijective (row : Fin 4) :
    Function.Bijective (correctionFiveRowMap row) := by
  fin_cases row <;> decide

private noncomputable def correctionFivePermutation (row : Fin 4) :
    Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (correctionFiveRowMap row) (correctionFiveRowMap_bijective row)

private def correctionFourRowMap : Fin 2 → Fin 4 → Fin 4 :=
  ![![3, 0, 2, 1], ![1, 0, 2, 3]]

private theorem correctionFourRowMap_bijective (row : Fin 2) :
    Function.Bijective (correctionFourRowMap row) := by
  fin_cases row <;> decide

private noncomputable def correctionFourPermutation (row : Fin 2) :
    Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (correctionFourRowMap row) (correctionFourRowMap_bijective row)

private noncomputable def correctionFiveSlots (k : ℕ) (row : Fin 4) (r : Fin k) :
    (Fin 5 ⊕ Fin k) ≃ Fin ((k + 1) + 4) :=
  ((correctionFivePermutation row).sumCongr (Equiv.refl (Fin k))).trans
    ((Equiv.swap (Sum.inr r : Fin 5 ⊕ Fin k) (Sum.inl 4)).trans
      (correctionFiveEquiv k))

private noncomputable def correctionRicciSlots (k : ℕ) :
    (Fin 4 ⊕ Fin (k + 1)) ≃ Fin ((k + 1) + 4) :=
  ((correctionFourPermutation 0).sumCongr (Equiv.refl (Fin (k + 1)))).trans
    ((Equiv.swap (Sum.inr (0 : Fin (k + 1)) : Fin 4 ⊕ Fin (k + 1))
      (Sum.inl 3)).trans (correctionFourEquiv k))

private noncomputable def correctionSpatialSlots (k : ℕ) (r : Fin k) :
    (Fin 4 ⊕ Fin (k + 1)) ≃ Fin ((k + 1) + 4) :=
  ((correctionFourPermutation 1).sumCongr (Equiv.refl (Fin (k + 1)))).trans
    ((Equiv.swap (Sum.inr (0 : Fin (k + 1)) : Fin 4 ⊕ Fin (k + 1))
      (Sum.inl 1)).trans
      ((Equiv.swap (Sum.inr r.succ : Fin 4 ⊕ Fin (k + 1)) (Sum.inl 3)).trans
        (correctionFourEquiv k)))

private noncomputable def baseReactionTerm (row : Fin 8) (negative : Bool) :
    ReactionTerm 0 where
  leftOrder := 0
  rightOrder := 0
  orders_eq := rfl
  negative := negative
  slots := finSumFinEquiv.trans (basePermutation row)

private noncomputable def baseReactionTerms : List (ReactionTerm 0) :=
  [baseReactionTerm 0 false, baseReactionTerm 0 false,
   baseReactionTerm 1 true, baseReactionTerm 1 true,
   baseReactionTerm 2 true, baseReactionTerm 2 true,
   baseReactionTerm 3 false, baseReactionTerm 3 false,
   baseReactionTerm 4 true, baseReactionTerm 5 true,
   baseReactionTerm 6 true, baseReactionTerm 7 true]

private noncomputable def derivativeCorrectionTerm (m : ℕ) (row : Fin 4)
    (r : Fin (4 + m)) : ReactionTerm (m + 1) where
  leftOrder := 1
  rightOrder := m
  orders_eq := Nat.add_comm 1 m
  negative := ![false, false, true, true] row
  slots := correctionFiveSlots (4 + m) row r

private noncomputable def spatialCorrectionTerm (m : ℕ) (r : Fin (4 + m)) :
    ReactionTerm (m + 1) where
  leftOrder := 0
  rightOrder := m + 1
  orders_eq := Nat.zero_add (m + 1)
  negative := true
  slots := correctionSpatialSlots (4 + m) r

private noncomputable def ricciCorrectionTerm (m : ℕ) : ReactionTerm (m + 1) where
  leftOrder := 0
  rightOrder := m + 1
  orders_eq := Nat.zero_add (m + 1)
  negative := true
  slots := correctionRicciSlots (4 + m)

private noncomputable def correctionBlock (m : ℕ) (r : Fin (4 + m)) :
    List (ReactionTerm (m + 1)) :=
  [derivativeCorrectionTerm m 0 r, derivativeCorrectionTerm m 1 r,
   derivativeCorrectionTerm m 2 r, spatialCorrectionTerm m r,
   spatialCorrectionTerm m r, derivativeCorrectionTerm m 3 r]

private noncomputable def correctionTerms (m : ℕ) :
    List (ReactionTerm (m + 1)) :=
  (List.ofFn (fun r : Fin (4 + m) ↦ correctionBlock m r)).flatten ++
    [ricciCorrectionTerm m]

set_option maxHeartbeats 2000000 in

private theorem baseReactionTerm_eval (D : LeviCivitaData g)
    (row : Fin 8) (negative : Bool) (x : M)
    (v : Fin 4 → TangentSpace (𝓡 n) x) :
    reactionTermEvaluation D (baseReactionTerm row negative) x v =
      let b := g.orthonormalBasis x
      let R := D.curvatureTensor x
      let C := ∑ p, ∑ q,
        (![R (v 0) (b p) (v 1) (b q) * R (v 2) (b p) (v 3) (b q),
           R (v 0) (b p) (v 1) (b q) * R (v 3) (b p) (v 2) (b q),
           R (v 0) (b p) (v 3) (b q) * R (v 1) (b p) (v 2) (b q),
           R (v 0) (b p) (v 2) (b q) * R (v 1) (b p) (v 3) (b q),
           R (v 0) (b p) (b q) (b p) * R (b q) (v 1) (v 2) (v 3),
           R (v 1) (b p) (b q) (b p) * R (v 0) (b q) (v 2) (v 3),
           R (v 2) (b p) (b q) (b p) * R (v 0) (v 1) (b q) (v 3),
           R (v 3) (b p) (b q) (b p) * R (v 0) (v 1) (v 2) (b q)] :
          Fin 8 → ℝ) row
      if negative = true then -C else C := by
  cases negative <;> fin_cases row <;> rfl

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem derivativeCorrectionTerm_eval (D : LeviCivitaData g)
    (m : ℕ) (row : Fin 4) (r : Fin (4 + m)) (x : M)
    (a : TangentSpace (𝓡 n) x)
    (v : Fin (4 + m) → TangentSpace (𝓡 n) x) :
    reactionTermEvaluation D (derivativeCorrectionTerm m row r) x (Fin.cons a v) =
      let b := g.orthonormalBasis x
      let H := D.covariantTensorDerivative D.riemannEvaluation x
      let T := D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
      ∑ p, ∑ q,
        (![H ![a, v r, b p, b q, b p] * T (Function.update v r (b q)),
           H ![v r, a, b p, b q, b p] * T (Function.update v r (b q)),
           -(H ![b q, a, b p, v r, b p] * T (Function.update v r (b q))),
           -(H ![b p, a, b p, b q, v r] * T (Function.update v r (b q)))] :
          Fin 4 → ℝ) row := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let W (p q : Fin d) : Fin ((4 + m + 1) + 4) → TangentSpace (𝓡 n) x :=
    Fin.append (Fin.cons a v) ![b p, b p, b q, b q]
  have hE (p q : Fin d) (z : Fin 5) :
      W p q (correctionFiveEquiv (4 + m) (Sum.inl z)) =
        (![a, b p, b p, b q, b q] : Fin 5 → TangentSpace (𝓡 n) x) z := by
    cases z using Fin.cases with
    | zero => simp [W, correctionFiveEquiv_inl_zero]
    | succ z =>
      rw [correctionFiveEquiv_inl_succ]
      simp only [W, Fin.append_right]
      rfl
  have hF (p q : Fin d) (s : Fin (4 + m)) :
      W p q (correctionFiveEquiv (4 + m) (Sum.inr s)) = v s := by
    simp [W, correctionFiveEquiv_inr]
  have hL (p q : Fin d) :
      (fun z : Fin 5 ↦ W p q (correctionFiveSlots (4 + m) row r (Sum.inl z))) =
        (![![a, v r, b p, b q, b p], ![v r, a, b p, b q, b p],
          ![b q, a, b p, v r, b p], ![b p, a, b p, b q, v r]] :
          Fin 4 → (Fin 5 → TangentSpace (𝓡 n) x)) row := by
    fin_cases row <;> funext z <;> fin_cases z <;>
      simp [correctionFiveSlots, correctionFivePermutation, correctionFiveRowMap,
        Equiv.sumCongr, Equiv.swap_apply_def, hE, hF]
  have hR (p q : Fin d) :
      (fun s : Fin (4 + m) ↦
        W p q (correctionFiveSlots (4 + m) row r (Sum.inr s))) =
        Function.update v r (b q) := by
    funext s
    by_cases hs : s = r
    · subst s
      simp [correctionFiveSlots, Equiv.sumCongr, hE]
    · simp [correctionFiveSlots, Equiv.sumCongr, Equiv.swap_apply_def, hF, hs]
  have hc : curvaturePairContraction D 1 m
      (correctionFiveSlots (4 + m) row r) x (Fin.cons a v) =
      ∑ p : Fin d, ∑ q : Fin d,
        D.covariantTensorDerivative D.riemannEvaluation x
          ((![![a, v r, b p, b q, b p], ![v r, a, b p, b q, b p],
            ![b q, a, b p, v r, b p], ![b p, a, b p, b q, v r]] :
            Fin 4 → (Fin 5 → TangentSpace (𝓡 n) x)) row) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (Function.update v r (b q)) := by
    change (∑ p : Fin d, ∑ q : Fin d,
      D.covariantTensorDerivative D.riemannEvaluation x
        (fun z ↦ W p q (correctionFiveSlots (4 + m) row r (Sum.inl z))) *
      D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
        (fun s ↦ W p q (correctionFiveSlots (4 + m) row r (Sum.inr s)))) = _
    simp only [hL, hR]
  simp only [reactionTermEvaluation, derivativeCorrectionTerm, hc]
  fin_cases row <;> simp [Finset.sum_neg_distrib, b, d]

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem spatialCorrectionTerm_eval (D : LeviCivitaData g)
    (m : ℕ) (r : Fin (4 + m)) (x : M)
    (a : TangentSpace (𝓡 n) x)
    (v : Fin (4 + m) → TangentSpace (𝓡 n) x) :
    reactionTermEvaluation D (spatialCorrectionTerm m r) x (Fin.cons a v) =
      let b := g.orthonormalBasis x;
      -(∑ p, ∑ q, D.curvatureTensor x a (b p) (b q) (v r) *
        D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
          (Fin.cons (b p) (Function.update v r (b q)))) := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let W (p q : Fin d) : Fin ((4 + m + 1) + 4) → TangentSpace (𝓡 n) x :=
    Fin.append (Fin.cons a v) ![b p, b p, b q, b q]
  have hE (p q : Fin d) (z : Fin 4) :
      W p q (correctionFourEquiv (4 + m) (Sum.inl z)) =
        (![b p, b p, b q, b q] : Fin 4 → TangentSpace (𝓡 n) x) z := by
    simp [W, correctionFourEquiv_inl]
  have hF (p q : Fin d) (s : Fin (4 + m + 1)) :
      W p q (correctionFourEquiv (4 + m) (Sum.inr s)) =
        (Fin.cons a v : Fin (4 + m + 1) → TangentSpace (𝓡 n) x) s := by
    simp [W, correctionFourEquiv_inr]
  have hL (p q : Fin d) :
      (fun z : Fin 4 ↦ W p q (correctionSpatialSlots (4 + m) r (Sum.inl z))) =
        (![a, b p, b q, v r] : Fin 4 → TangentSpace (𝓡 n) x) := by
    funext z
    fin_cases z <;>
      simp [correctionSpatialSlots, correctionFourPermutation, correctionFourRowMap,
        Equiv.sumCongr, Equiv.swap_apply_def, hE, hF, Ne.symm (Fin.succ_ne_zero r)]
  have hR (p q : Fin d) :
      (fun s : Fin (4 + m + 1) ↦
        W p q (correctionSpatialSlots (4 + m) r (Sum.inr s))) =
        Fin.cons (b p) (Function.update v r (b q)) := by
    funext s
    cases s using Fin.cases with
    | zero =>
      simp [correctionSpatialSlots, Equiv.sumCongr, Equiv.swap_apply_def,
        hE]
    | succ s =>
      by_cases hs : s = r
      · subst s
        simp [correctionSpatialSlots, Equiv.sumCongr, Equiv.swap_apply_def, hE]
      · simp [correctionSpatialSlots, Equiv.sumCongr, Equiv.swap_apply_def,
          hF, hs]
  simp only [reactionTermEvaluation, spatialCorrectionTerm, if_true,
    curvaturePairContraction]
  change -(∑ p : Fin d, ∑ q : Fin d,
    D.riemannEvaluation x
      (fun z ↦ W p q (correctionSpatialSlots (4 + m) r (Sum.inl z))) *
    D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
      (fun s ↦ W p q (correctionSpatialSlots (4 + m) r (Sum.inr s)))) = _
  apply congrArg (fun z : ℝ ↦ -z)
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hleft : D.riemannEvaluation x
      (fun z ↦ W p q (correctionSpatialSlots (4 + m) r (Sum.inl z))) =
      D.riemannEvaluation x (![a, b p, b q, v r] : Fin 4 → TangentSpace (𝓡 n) x) := by
    exact congrArg (D.riemannEvaluation x) (hL p q)
  have hright : D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
      (fun s ↦ W p q (correctionSpatialSlots (4 + m) r (Sum.inr s))) =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
        (Fin.cons (b p) (Function.update v r (b q))) := by
    exact congrArg
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x)
      (hR p q)
  exact congrArg₂ (· * ·) hleft hright

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem ricciCorrectionTerm_eval (D : LeviCivitaData g)
    (m : ℕ) (x : M) (a : TangentSpace (𝓡 n) x)
    (v : Fin (4 + m) → TangentSpace (𝓡 n) x) :
    reactionTermEvaluation D (ricciCorrectionTerm m) x (Fin.cons a v) =
      let b := g.orthonormalBasis x;
      -(∑ p, ∑ q, D.curvatureTensor x a (b p) (b q) (b p) *
        D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
          (Fin.cons (b q) v)) := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let W (p q : Fin d) : Fin ((4 + m + 1) + 4) → TangentSpace (𝓡 n) x :=
    Fin.append (Fin.cons a v) ![b p, b p, b q, b q]
  have hE (p q : Fin d) (z : Fin 4) :
      W p q (correctionFourEquiv (4 + m) (Sum.inl z)) =
        (![b p, b p, b q, b q] : Fin 4 → TangentSpace (𝓡 n) x) z := by
    simp [W, correctionFourEquiv_inl]
  have hF (p q : Fin d) (s : Fin (4 + m + 1)) :
      W p q (correctionFourEquiv (4 + m) (Sum.inr s)) =
        (Fin.cons a v : Fin (4 + m + 1) → TangentSpace (𝓡 n) x) s := by
    simp [W, correctionFourEquiv_inr]
  have hL (p q : Fin d) :
      (fun z : Fin 4 ↦ W p q (correctionRicciSlots (4 + m) (Sum.inl z))) =
        (![a, b p, b q, b p] : Fin 4 → TangentSpace (𝓡 n) x) := by
    funext z
    fin_cases z <;>
      simp [correctionRicciSlots, correctionFourPermutation, correctionFourRowMap,
        Equiv.sumCongr, Equiv.swap_apply_def, hE, hF]
  have hR (p q : Fin d) :
      (fun s : Fin (4 + m + 1) ↦
        W p q (correctionRicciSlots (4 + m) (Sum.inr s))) = Fin.cons (b q) v := by
    funext s
    cases s using Fin.cases <;>
      simp [correctionRicciSlots, Equiv.sumCongr, Equiv.swap_apply_def, hE, hF]
  simp only [reactionTermEvaluation, ricciCorrectionTerm, if_true,
    curvaturePairContraction]
  change -(∑ p : Fin d, ∑ q : Fin d,
    D.riemannEvaluation x
      (fun z ↦ W p q (correctionRicciSlots (4 + m) (Sum.inl z))) *
    D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
      (fun s ↦ W p q (correctionRicciSlots (4 + m) (Sum.inr s)))) = _
  apply congrArg (fun z : ℝ ↦ -z)
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hleft : D.riemannEvaluation x
      (fun z ↦ W p q (correctionRicciSlots (4 + m) (Sum.inl z))) =
      D.riemannEvaluation x (![a, b p, b q, b p] : Fin 4 → TangentSpace (𝓡 n) x) := by
    exact congrArg (D.riemannEvaluation x) (hL p q)
  have hright : D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
      (fun s ↦ W p q (correctionRicciSlots (4 + m) (Sum.inr s))) =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
        (Fin.cons (b q) v) := by
    exact congrArg
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x)
      (hR p q)
  exact congrArg₂ (· * ·) hleft hright

private theorem baseReactionTerms_length : baseReactionTerms.length = 12 := by
  rfl

private theorem correctionBlock_length (m : ℕ) (r : Fin (4 + m)) :
    (correctionBlock m r).length = 6 := by
  rfl

private theorem correctionTerms_length (m : ℕ) :
    (correctionTerms m).length = 6 * (4 + m) + 1 := by
  simp [correctionTerms, List.length_flatten, List.map_ofFn,
    Function.comp_def, correctionBlock_length, Nat.mul_comm]

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem baseReactionTerms_eval (D : LeviCivitaData g) :
    (fun (x : M) (v : Fin 4 → TangentSpace (𝓡 n) x) ↦
      D.curvatureReaction x (v 0) (v 1) (v 2) (v 3)) =
      reactionListEvaluation D baseReactionTerms := by
  classical
  funext x v
  let b := g.orthonormalBasis x
  have htrace (u : TangentSpace (𝓡 n) x) (f : TangentSpace (𝓡 n) x → ℝ) :
      (∑ q, D.ricci x u (b q) * f (b q)) =
        ∑ p, ∑ q, D.curvatureTensor x u (b p) (b q) (b p) * f (b q) := by
    simp only [LeviCivitaData.ricci, b, Finset.sum_mul]
    rw [Finset.sum_comm]
  simp only [reactionListEvaluation, baseReactionTerms, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, baseReactionTerm_eval]
  simp only [Matrix.cons_val, Bool.false_eq_true, if_false, if_true]
  simp only [LeviCivitaData.curvatureReaction, LeviCivitaData.curvatureB,
    Finset.sum_add_distrib]
  rw [htrace (v 0) (fun z ↦ D.curvatureTensor x z (v 1) (v 2) (v 3)),
    htrace (v 1) (fun z ↦ D.curvatureTensor x (v 0) z (v 2) (v 3)),
    htrace (v 2) (fun z ↦ D.curvatureTensor x (v 0) (v 1) z (v 3)),
    htrace (v 3) (fun z ↦ D.curvatureTensor x (v 0) (v 1) (v 2) z)]
  ring

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem correctionTerms_eval (D : LeviCivitaData g) (m : ℕ) :
    tensorHeatCorrection D
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) =
      reactionListEvaluation D (correctionTerms m) := by
  classical
  funext x V
  obtain ⟨a, v, rfl⟩ := Fin.exists_cons V
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let H := D.covariantTensorDerivative D.riemannEvaluation x
  let T := D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
  let K := D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
  have htime0 :
      (∑ r : Fin (4 + m), ∑ q : Fin d, ∑ p : Fin d,
        H ![a, v r, b p, b q, b p] * T (Function.update v r (b q))) =
      ∑ r : Fin (4 + m), ∑ p : Fin d, ∑ q : Fin d,
        H ![a, v r, b p, b q, b p] * T (Function.update v r (b q)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
  have htime1 :
      (∑ r : Fin (4 + m), ∑ q : Fin d, ∑ p : Fin d,
        H ![v r, a, b p, b q, b p] * T (Function.update v r (b q))) =
      ∑ r : Fin (4 + m), ∑ p : Fin d, ∑ q : Fin d,
        H ![v r, a, b p, b q, b p] * T (Function.update v r (b q)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
  have htime2 :
      (∑ r : Fin (4 + m), ∑ q : Fin d, ∑ p : Fin d,
        H ![b q, a, b p, v r, b p] * T (Function.update v r (b q))) =
      ∑ r : Fin (4 + m), ∑ p : Fin d, ∑ q : Fin d,
        H ![b q, a, b p, v r, b p] * T (Function.update v r (b q)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
  have hspatial :
      (∑ p : Fin d, ∑ r : Fin (4 + m), ∑ q : Fin d,
        D.curvatureTensor x a (b p) (b q) (v r) *
          K (Fin.cons (b p) (Function.update v r (b q)))) =
      ∑ r : Fin (4 + m), ∑ p : Fin d, ∑ q : Fin d,
        D.curvatureTensor x a (b p) (b q) (v r) *
          K (Fin.cons (b p) (Function.update v r (b q))) := by
    rw [Finset.sum_comm]
  have hderivative :
      (∑ p : Fin d, ∑ r : Fin (4 + m), ∑ q : Fin d,
        H ![b p, a, b p, b q, v r] * T (Function.update v r (b q))) =
      ∑ r : Fin (4 + m), ∑ p : Fin d, ∑ q : Fin d,
        H ![b p, a, b p, b q, v r] * T (Function.update v r (b q)) := by
    rw [Finset.sum_comm]
  simp only [K, LeviCivitaData.iteratedCovariantTensorDerivative] at hspatial
  dsimp only [H, T, b] at htime0 htime1 htime2 hspatial hderivative
  simp only [reactionListEvaluation, correctionTerms, List.map_append, List.sum_append,
    List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, correctionBlock, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, derivativeCorrectionTerm_eval, spatialCorrectionTerm_eval,
    ricciCorrectionTerm_eval]
  simp only [Matrix.cons_val, tensorHeatCorrection, Fin.cons_zero, Fin.cons_succ,
    ricci_covariantDerivative_curvature_trace, add_mul, sub_mul,
    Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, add_zero]
  rw [htime0, htime1, htime2, hspatial, hderivative]
  simp only [LeviCivitaData.iteratedCovariantTensorDerivative, d]
  ring

theorem curvatureReaction_base_expansion (D : LeviCivitaData g) :
    ∃ L : List (ReactionTerm 0), L.length = 12 ∧
      (fun (x : M) (v : Fin 4 → TangentSpace (𝓡 n) x) ↦
        D.curvatureReaction x (v 0) (v 1) (v 2) (v 3)) =
        reactionListEvaluation D L := by
  exact ⟨baseReactionTerms, baseReactionTerms_length, baseReactionTerms_eval D⟩

theorem tensorHeatCorrection_expansion (D : LeviCivitaData g) (m : ℕ) :
    ∃ L : List (ReactionTerm (m + 1)), L.length = 6 * (4 + m) + 1 ∧
      tensorHeatCorrection D
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) =
        reactionListEvaluation D L := by
  exact ⟨correctionTerms m, correctionTerms_length m, correctionTerms_eval D m⟩


end PoincareConjecture.M04
