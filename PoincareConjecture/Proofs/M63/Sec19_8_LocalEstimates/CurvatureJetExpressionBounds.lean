import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetErrorExpressions
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.RicciArcExpressions
import PoincareConjecture.Proofs.M62.Cor0_3_PointwiseBounds
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Cast

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63CurvatureJet_ambientError_abs_le
    (F : RicciFlow n M (Icc a b)) (c : ℝ -> ℝ -> M)
    (hc : M62ShrinkingCurve F c) (m : Nat)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hLower : ∀ i, i < m ->
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c i t x) ≤ L)
    (hRm : ∀ d, d ≤ m -> ∀ v : Fin (4 + d) -> TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) ->
        |(F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).riemannEvaluation d (c x t) v| ≤ K)
    (hRic : ∀ d, d ≤ m + 1 -> ∀ v : Fin (2 + d) -> TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) ->
        |(F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).ricciEvaluation d (c x t) v| ≤ K)
    (Z : (y : ℝ) -> TangentSpace (𝓡 n) (c y t)) :
    let D := F.connection t
    let w := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c m t x)
    |m63MarkedTensorExpression F c D.riemannEvaluation
        (m63RiemannJetErrorExpression m) t Z x +
      m63MarkedTensorExpression F c D.ricciEvaluation
        (m63RicciJetErrorExpression m) t Z x| ≤
      (m63JetErrorMassBound m : ℝ) * K * L ^ (m + 3) * (1 + w) *
        (F.metric t).tangentNorm (c x t) (Z x) := by
  classical
  let D := F.connection t
  let V : Nat -> TangentSpace (𝓡 n) (c x t) := fun i =>
    match i with
    | 0 => spatialUnitTangent F c t x
    | r + 1 => m63CurvatureJet F c r t x
  let N := fun i => (F.metric t).tangentNorm (c x t) (V i)
  let w := N (m + 1)
  let z := (F.metric t).tangentNorm (c x t) (Z x)
  let C := K * L ^ (m + 3) * (1 + w) * z
  have hN (i : Nat) : 0 ≤ N i := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hNzero : N 0 = 1 := unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x
  have hNlower (i : Nat) (hi : i ≤ m) : N i ≤ L := by
    cases i with
    | zero => exact hNzero.le.trans hL
    | succ i => exact hLower i (by omega)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hpow : 1 ≤ L ^ (m + 3) := by
    simpa only [pow_zero] using pow_le_pow_right₀ hL (Nat.zero_le (m + 3))
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (mul_nonneg hK (pow_nonneg hL0 _))
      (add_nonneg zero_le_one (hN (m + 1)))) hz
  have hprod {k : Nat} (s : Finset (Fin k)) (f : Fin k -> Nat)
      (hweight : ∑ i ∈ s, f i ≤ m + 1) (hcard : s.card ≤ m + 3) :
      ∏ i ∈ s, N (f i) ≤ L ^ (m + 3) * (1 + w) := by
    by_cases hex : ∃ i ∈ s, f i = m + 1
    · obtain ⟨i, hi, hfi⟩ := hex
      have hsum := Finset.sum_erase_add s f hi
      have hzero (j : Fin k) (hj : j ∈ s.erase i) : f j = 0 := by
        have hle := Finset.single_le_sum (fun r _ => Nat.zero_le (f r)) hj
        omega
      have hrest : ∏ j ∈ s.erase i, N (f j) = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        rw [hzero j hj, hNzero]
      rw [← Finset.prod_erase_mul s (fun j => N (f j)) hi, hrest, one_mul, hfi]
      change w ≤ _
      have hw := hN (m + 1)
      change 0 ≤ w at hw
      nlinarith only [hpow, hw]
    · have hsmall (i : Fin k) (hi : i ∈ s) : f i ≤ m := by
        have hle := Finset.single_le_sum (fun r _ => Nat.zero_le (f r)) hi
        have hne : f i ≠ m + 1 := fun h => hex ⟨i, hi, h⟩
        omega
      have hp := Finset.prod_le_prod (fun i _ => hN (f i))
        (fun i hi => hNlower (f i) (hsmall i hi))
      have hp' : ∏ i ∈ s, N (f i) ≤ L ^ (m + 3) := by
        exact (hp.trans_eq (Finset.prod_const L)).trans (pow_le_pow_right₀ hL hcard)
      have hw := hN (m + 1)
      change 0 ≤ w at hw
      nlinarith only [hp', hpow, hw]
  have hterm {k : Nat} (T : CovariantTensorEvaluation n M k)
      (hT : IsSmoothCovariantTensor T) (A : MarkedTensorContraction k)
      (hweight : A.weight = m + 1) (hrank : k + A.order ≤ m + 4)
      (hbound : ∀ v : Fin (k + A.order) -> TangentSpace (𝓡 n) (c x t),
        (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) ->
          |D.iteratedCovariantTensorDerivative T A.order (c x t) v| ≤ K) :
      |m63MarkedTensorTerm F c T A t Z x| ≤ C := by
    have hiter (d : Nat) : IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative T d) := by
      induction d with
      | zero => exact hT
      | succ d ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative D ih
    let vec := fun i => if i = A.test then Z x else V (A.jet i)
    have hb := tensor_abs_le_of_unit_bound (F.metric t)
      (D.iteratedCovariantTensorDerivative T A.order) (hiter _) (c x t) hbound vec
    have hp := hprod (Finset.univ.erase A.test) A.jet
      ((Nat.le_add_left _ _).trans_eq hweight)
      (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]; omega)
    have heq : (∏ i, (F.metric t).tangentNorm (c x t) (vec i)) =
        (∏ i ∈ Finset.univ.erase A.test, N (A.jet i)) * z := by
      rw [← Finset.prod_erase_mul Finset.univ
        (fun i => (F.metric t).tangentNorm (c x t) (vec i)) (Finset.mem_univ A.test)]
      have hmark : (F.metric t).tangentNorm (c x t) (vec A.test) = z := by
        simp only [vec, if_true, z]
      rw [hmark]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      simp only [vec, (Finset.mem_erase.mp hi).1, if_false]
      rfl
    rw [heq] at hb
    change |m63MarkedTensorTerm F c T A t Z x| ≤ _ at hb
    calc
      _ ≤ K * ((∏ i ∈ Finset.univ.erase A.test, N (A.jet i)) * z) := hb
      _ ≤ K * ((L ^ (m + 3) * (1 + w)) * z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hz) hK
      _ = C := by dsimp only [C]; ring
  have hlist {k : Nat} (T : CovariantTensorEvaluation n M k)
      (P : List (Int × MarkedTensorContraction k))
      (hP : ∀ q ∈ P, |m63MarkedTensorTerm F c T q.2 t Z x| ≤ C) :
      |m63MarkedTensorExpression F c T P t Z x| ≤ (markedTensorCoefficientMass P : ℝ) * C := by
    induction P with
    | nil => simp [m63MarkedTensorExpression, markedTensorCoefficientMass]
    | cons q P ih =>
      have hp := ih (fun r hr => hP r (List.mem_cons_of_mem q hr))
      have hq := mul_le_mul_of_nonneg_left (hP q List.mem_cons_self) (abs_nonneg (q.1 : ℝ))
      have hcast : |(q.1 : ℝ)| = (q.1.natAbs : ℝ) := by
        simp only [Nat.cast_natAbs, Int.cast_abs]
      rw [← abs_mul, hcast] at hq
      change |(q.1 : ℝ) * m63MarkedTensorTerm F c T q.2 t Z x +
        m63MarkedTensorExpression F c T P t Z x| ≤ _
      calc
        _ ≤ |(q.1 : ℝ) * m63MarkedTensorTerm F c T q.2 t Z x| +
            |m63MarkedTensorExpression F c T P t Z x| := abs_add_le _ _
        _ ≤ (q.1.natAbs : ℝ) * C + (markedTensorCoefficientMass P : ℝ) * C :=
          add_le_add hq hp
        _ = _ := by simp only [markedTensorCoefficientMass, List.map_cons,
          List.sum_cons, Nat.cast_add, add_mul]
  have hs := m63JetErrorExpression_spec m
  have hr := hlist D.riemannEvaluation (m63RiemannJetErrorExpression m) (by
    intro q hq
    exact hterm _ (M04.isSmoothCovariantTensor_riemannEvaluation D) q.2 (hs.1 q hq).1
      (by have := (hs.1 q hq).2; omega) (hRm q.2.order (hs.1 q hq).2))
  have hi := hlist D.ricciEvaluation (m63RicciJetErrorExpression m) (by
    intro q hq
    exact hterm _ (M04.isSmoothCovariantTensor_ricciEvaluation D) q.2 (hs.2.1 q hq).1
      (by have := (hs.2.1 q hq).2; omega) (hRic q.2.order (hs.2.1 q hq).2))
  have hmass : (markedTensorCoefficientMass (m63RiemannJetErrorExpression m) : ℝ) +
      (markedTensorCoefficientMass (m63RicciJetErrorExpression m) : ℝ) ≤
        (m63JetErrorMassBound m : ℝ) := by exact_mod_cast hs.2.2
  have hsum := (abs_add_le _ _).trans (add_le_add hr hi)
  have hfinal := hsum.trans (by
    simpa only [add_mul] using mul_le_mul_of_nonneg_right hmass hC)
  dsimp only [C, w, N, V] at hfinal
  dsimp only
  simpa only [D, z, mul_assoc] using hfinal

theorem m63TangentRicci_arc_iterate_abs_le [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ -> ℝ -> M)
    (hc : M62ShrinkingCurve F c) (m : Nat)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hLower : ∀ i, i < m ->
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c i t x) ≤ L)
    (hRic : ∀ d, d ≤ m + 1 -> ∀ v : Fin (2 + d) -> TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) ->
        |(F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).ricciEvaluation d (c x t) v| ≤ K) :
    let B := (Nat.factorial (m + 3) : ℝ) * K * L ^ (m + 3)
    let w := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c m t x)
    (∀ j, j ≤ m ->
      |((m62ArcDerivative F c t)^[j]) (m62TangentRicci F c t) x| ≤ B) ∧
    |((m62ArcDerivative F c t)^[m + 1]) (m62TangentRicci F c t) x| ≤ B * (1 + w) := by
  classical
  let D := F.connection t
  let V : Nat -> TangentSpace (𝓡 n) (c x t) := fun i =>
    match i with
    | 0 => spatialUnitTangent F c t x
    | r + 1 => m63CurvatureJet F c r t x
  let N := fun i => (F.metric t).tangentNorm (c x t) (V i)
  let w := N (m + 1)
  let ev := fun A : MarkedTensorContraction 2 =>
    D.iteratedCovariantTensorDerivative D.ricciEvaluation A.order (c x t)
      (fun i => V (A.jet i))
  have hN (i : Nat) : 0 ≤ N i := Real.sqrt_nonneg _
  have hNzero : N 0 = 1 := unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x
  have hNlower (i : Nat) (hi : i ≤ m) : N i ≤ L := by
    cases i with
    | zero => exact hNzero.le.trans hL
    | succ i => exact hLower i (by omega)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hpow : 1 ≤ L ^ (m + 3) := by
    simpa only [pow_zero] using pow_le_pow_right₀ hL (Nat.zero_le (m + 3))
  have hprodLower {k : Nat} (s : Finset (Fin k)) (f : Fin k -> Nat)
      (hweight : ∑ i ∈ s, f i ≤ m) (hcard : s.card ≤ m + 3) :
      ∏ i ∈ s, N (f i) ≤ L ^ (m + 3) := by
    have hsmall (i : Fin k) (hi : i ∈ s) : f i ≤ m :=
      (Finset.single_le_sum (fun r _ => Nat.zero_le (f r)) hi).trans hweight
    have hp := Finset.prod_le_prod (fun i _ => hN (f i))
      (fun i hi => hNlower (f i) (hsmall i hi))
    exact (hp.trans_eq (Finset.prod_const L)).trans (pow_le_pow_right₀ hL hcard)
  have hprodTop {k : Nat} (s : Finset (Fin k)) (f : Fin k -> Nat)
      (hweight : ∑ i ∈ s, f i ≤ m + 1) (hcard : s.card ≤ m + 3) :
      ∏ i ∈ s, N (f i) ≤ L ^ (m + 3) * (1 + w) := by
    by_cases hex : ∃ i ∈ s, f i = m + 1
    · obtain ⟨i, hi, hfi⟩ := hex
      have hsum := Finset.sum_erase_add s f hi
      have hzero (j : Fin k) (hj : j ∈ s.erase i) : f j = 0 := by
        have hle := Finset.single_le_sum (fun r _ => Nat.zero_le (f r)) hj
        omega
      have hrest : ∏ j ∈ s.erase i, N (f j) = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        rw [hzero j hj, hNzero]
      rw [← Finset.prod_erase_mul s (fun j => N (f j)) hi, hrest, one_mul, hfi]
      change w ≤ _
      have hw := hN (m + 1)
      change 0 ≤ w at hw
      nlinarith only [hpow, hw]
    · have hsmall (i : Fin k) (hi : i ∈ s) : f i ≤ m := by
        have hle := Finset.single_le_sum (fun r _ => Nat.zero_le (f r)) hi
        have hne : f i ≠ m + 1 := fun h => hex ⟨i, hi, h⟩
        omega
      have hp := Finset.prod_le_prod (fun i _ => hN (f i))
        (fun i hi => hNlower (f i) (hsmall i hi))
      have hp' := (hp.trans_eq (Finset.prod_const L)).trans (pow_le_pow_right₀ hL hcard)
      have hw := hN (m + 1)
      change 0 ≤ w at hw
      nlinarith only [hp', hpow, hw]
  have hiter (d : Nat) :
      IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative D.ricciEvaluation d) := by
    induction d with
    | zero => exact M04.isSmoothCovariantTensor_ricciEvaluation D
    | succ d ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative D ih
  have hterm (A : MarkedTensorContraction 2) (horder : A.order ≤ m + 1) :
      (∑ i, A.jet i ≤ m -> |ev A| ≤ K * L ^ (m + 3)) ∧
      (∑ i, A.jet i ≤ m + 1 -> |ev A| ≤ K * L ^ (m + 3) * (1 + w)) := by
    have hb := tensor_abs_le_of_unit_bound (F.metric t)
      (D.iteratedCovariantTensorDerivative D.ricciEvaluation A.order)
      (hiter _) (c x t) (hRic A.order horder) (fun i => V (A.jet i))
    change |ev A| ≤ K * ∏ i, N (A.jet i) at hb
    have hcard : (Finset.univ : Finset (Fin (2 + A.order))).card ≤ m + 3 := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    constructor
    · intro hweight
      exact hb.trans (mul_le_mul_of_nonneg_left
        (hprodLower Finset.univ A.jet hweight hcard) hK)
    · intro hweight
      exact (hb.trans (mul_le_mul_of_nonneg_left
        (hprodTop Finset.univ A.jet hweight hcard) hK)).trans_eq (by ring)
  have hlist (P : List (Int × MarkedTensorContraction 2)) {C : ℝ}
      (hP : ∀ q ∈ P, |ev q.2| ≤ C) :
      |m63UnmarkedTensorExpression F c D.ricciEvaluation P t x| ≤
        (markedTensorCoefficientMass P : ℝ) * C := by
    induction P with
    | nil => simp [m63UnmarkedTensorExpression, markedTensorCoefficientMass]
    | cons q P ih =>
      have hp := ih (fun r hr => hP r (List.mem_cons_of_mem q hr))
      have hq := mul_le_mul_of_nonneg_left (hP q List.mem_cons_self) (abs_nonneg (q.1 : ℝ))
      have hcast : |(q.1 : ℝ)| = (q.1.natAbs : ℝ) := by
        simp only [Nat.cast_natAbs, Int.cast_abs]
      rw [← abs_mul, hcast] at hq
      change |(q.1 : ℝ) * ev q.2 +
        m63UnmarkedTensorExpression F c D.ricciEvaluation P t x| ≤ _
      calc
        _ ≤ |(q.1 : ℝ) * ev q.2| +
            |m63UnmarkedTensorExpression F c D.ricciEvaluation P t x| := abs_add_le _ _
        _ ≤ (q.1.natAbs : ℝ) * C + (markedTensorCoefficientMass P : ℝ) * C :=
          add_le_add hq hp
        _ = _ := by simp only [markedTensorCoefficientMass, List.map_cons,
          List.sum_cons, Nat.cast_add, add_mul]
  have hmass (j : Nat) (hj : j ≤ m + 1) :
      (markedTensorCoefficientMass (m63RicciArcExpression j) : ℝ) ≤
        (Nat.factorial (m + 3) : ℝ) := by
    exact_mod_cast (m63RicciArcExpression_spec j).2.2.2.trans
      (Nat.factorial_le (by omega : j + 2 ≤ m + 3))
  dsimp only
  constructor
  · intro j hj
    rw [(m63TangentRicci_arc_iterate F c hc j ht x).1]
    have hbound := hlist (m63RicciArcExpression j) (by
      intro q hq
      have hs := (m63RicciArcExpression_spec j).1 q hq
      exact (hterm q.2 (by omega)).1 (by omega))
    calc
      _ ≤ (markedTensorCoefficientMass (m63RicciArcExpression j) : ℝ) *
          (K * L ^ (m + 3)) := hbound
      _ ≤ (Nat.factorial (m + 3) : ℝ) * (K * L ^ (m + 3)) :=
        mul_le_mul_of_nonneg_right (hmass j (by omega)) (by positivity)
      _ = _ := by ring
  · rw [(m63TangentRicci_arc_iterate F c hc (m + 1) ht x).1]
    have hbound := hlist (m63RicciArcExpression (m + 1)) (by
      intro q hq
      have hs := (m63RicciArcExpression_spec (m + 1)).1 q hq
      exact (hterm q.2 hs.2).2 (by omega))
    calc
      _ ≤ (markedTensorCoefficientMass (m63RicciArcExpression (m + 1)) : ℝ) *
          (K * L ^ (m + 3) * (1 + w)) := hbound
      _ ≤ (Nat.factorial (m + 3) : ℝ) * (K * L ^ (m + 3) * (1 + w)) :=
        mul_le_mul_of_nonneg_right (hmass (m + 1) le_rfl)
          (mul_nonneg (mul_nonneg hK (pow_nonneg hL0 _))
            (add_nonneg zero_le_one (hN (m + 1))))
      _ = _ := by dsimp only [w, N, V]; ring

end PoincareConjecture
