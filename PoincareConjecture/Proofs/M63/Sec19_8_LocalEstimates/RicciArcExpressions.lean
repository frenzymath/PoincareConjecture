import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.MarkedTensorDerivative
import Mathlib.Data.Nat.Factorial.Basic










set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62


noncomputable def m63RicciArcExpression : Nat -> List (Int × MarkedTensorContraction 2)
  | 0 => [(1, { order := 0, test := 0, jet := ![0, 0] })]
  | j + 1 =>
      markedTensorExpressionDerivative (m63RicciArcExpression j) ++
        (m63RicciArcExpression j).map (fun q => (q.1, q.2.slotStep q.2.test))

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}


noncomputable def m63UnmarkedTensorExpression
    (F : RicciFlow n M (Icc a b)) (c : ℝ -> ℝ -> M)
    {k : Nat} (T : CovariantTensorEvaluation n M k)
    (P : List (Int × MarkedTensorContraction k)) (t x : ℝ) : ℝ :=
  let K : Nat -> TangentSpace (𝓡 n) (c x t) := fun r =>
    match r with
    | 0 => spatialUnitTangent F c t x
    | i + 1 => m63CurvatureJet F c i t x
  (P.map (fun q => (q.1 : ℝ) *
    (F.connection t).iteratedCovariantTensorDerivative T q.2.order (c x t)
      (fun i => K (q.2.jet i)))).sum




theorem m63RicciArcExpression_spec (j : Nat) :
    (∀ q ∈ m63RicciArcExpression j,
      q.2.order + ∑ i, q.2.jet i = j ∧ q.2.order ≤ j) ∧
    markedTensorCoefficientMass (m63RicciArcExpression (j + 1)) =
      ((m63RicciArcExpression j).map (fun q => q.1.natAbs * (3 + q.2.order))).sum ∧
    markedTensorCoefficientMass (m63RicciArcExpression (j + 1)) ≤
      (j + 3) * markedTensorCoefficientMass (m63RicciArcExpression j) ∧
    markedTensorCoefficientMass (m63RicciArcExpression j) ≤ Nat.factorial (j + 2) := by
  classical
  have hslot (A : MarkedTensorContraction 2) (i : Fin (2 + A.order)) :
      ∑ z, (A.slotStep i).jet z = (∑ z, A.jet z) + 1 := by
    have hold := Finset.sum_erase_add Finset.univ A.jet (Finset.mem_univ i)
    have hnew := Finset.sum_erase_add Finset.univ
      (Function.update A.jet i (A.jet i + 1)) (Finset.mem_univ i)
    have heq : ∑ z ∈ Finset.univ.erase i, Function.update A.jet i (A.jet i + 1) z =
        ∑ z ∈ Finset.univ.erase i, A.jet z := by
      apply Finset.sum_congr rfl
      intro z hz
      exact Function.update_of_ne (Finset.mem_erase.mp hz).1 _ _
    rw [heq, Function.update_self] at hnew
    change (∑ z, Function.update A.jet i (A.jet i + 1) z) = _
    omega
  have hbranch (A : MarkedTensorContraction 2) (B : MarkedTensorContraction 2)
      (hB : B ∈ A.derivativeBranches) :
      B.order + ∑ i, B.jet i = (A.order + ∑ i, A.jet i) + 1 := by
    rcases List.mem_cons.mp hB with rfl | hB
    · change A.order + 1 +
        (∑ i : Fin ((2 + A.order) + 1), Fin.cons 0 A.jet i) = _
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Nat.zero_add]
      omega
    · obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hB
      rw [hslot]
      rfl
  have hinvariant (j : Nat) : ∀ q ∈ m63RicciArcExpression j,
      q.2.order + ∑ i, q.2.jet i = j ∧ q.2.order ≤ j := by
    induction j with
    | zero =>
      intro q hq
      have hq := List.mem_singleton.mp hq
      subst q
      exact ⟨by decide, by decide⟩
    | succ j ih =>
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨r, hr, hq⟩ := List.mem_flatMap.mp hq
        obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hq
        have h := hbranch r.2 A hA
        have horder := r.2.derivativeBranches_spec.2 A hA
        have hi := ih r hr
        change A.order + (∑ i, A.jet i) = j + 1 ∧ A.order ≤ j + 1
        exact ⟨by omega, by omega⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        have hi := ih r hr
        have hs := hslot r.2 r.2.test
        constructor
        · change r.2.order + (∑ i, (r.2.slotStep r.2.test).jet i) = j + 1
          rw [hslot]
          omega
        · exact hi.2.trans (Nat.le_succ j)
  have hrepeat (z : Int) (P : List (MarkedTensorContraction 2)) :
      markedTensorCoefficientMass (P.map (fun A => (z, A))) = z.natAbs * P.length := by
    induction P with
    | nil => simp [markedTensorCoefficientMass]
    | cons A P ih =>
      change z.natAbs + markedTensorCoefficientMass (P.map (fun B => (z, B))) = _
      rw [ih, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
  have hmass (P : List (Int × MarkedTensorContraction 2)) :
      markedTensorCoefficientMass (markedTensorExpressionDerivative P) =
        (P.map (fun q => q.1.natAbs * (2 + q.2.order))).sum := by
    induction P with
    | nil => rfl
    | cons q P ih =>
      change markedTensorCoefficientMass
        (q.2.derivativeBranches.map (fun A => (q.1, A)) ++
          markedTensorExpressionDerivative P) = _
      rw [show ∀ L R : List (Int × MarkedTensorContraction 2),
          markedTensorCoefficientMass (L ++ R) =
            markedTensorCoefficientMass L + markedTensorCoefficientMass R by
        intro L R
        simp only [markedTensorCoefficientMass, List.map_append, List.sum_append]]
      rw [hrepeat, q.2.derivativeBranches_spec.1, ih]
      rfl
  have hnext (j : Nat) :
      markedTensorCoefficientMass (m63RicciArcExpression (j + 1)) =
        ((m63RicciArcExpression j).map (fun q => q.1.natAbs * (3 + q.2.order))).sum := by
    change markedTensorCoefficientMass
      (markedTensorExpressionDerivative (m63RicciArcExpression j) ++ _) = _
    simp only [markedTensorCoefficientMass, List.map_append, List.sum_append,
      List.map_map, Function.comp_def]
    change markedTensorCoefficientMass
      (markedTensorExpressionDerivative (m63RicciArcExpression j)) +
        markedTensorCoefficientMass (m63RicciArcExpression j) = _
    rw [hmass]
    generalize m63RicciArcExpression j = P
    induction P with
    | nil => rfl
    | cons q P ih =>
      simp only [List.map_cons, List.sum_cons, markedTensorCoefficientMass] at ih ⊢
      nlinarith only [ih]
  have hbound (j : Nat) :
      markedTensorCoefficientMass (m63RicciArcExpression (j + 1)) ≤
        (j + 3) * markedTensorCoefficientMass (m63RicciArcExpression j) := by
    rw [hnext]
    have hlist (P : List (Int × MarkedTensorContraction 2))
        (hP : ∀ q ∈ P, q.2.order ≤ j) :
        (P.map (fun q => q.1.natAbs * (3 + q.2.order))).sum ≤
          (j + 3) * markedTensorCoefficientMass P := by
      induction P with
      | nil => simp [markedTensorCoefficientMass]
      | cons q P ih =>
        have hq := Nat.mul_le_mul_left q.1.natAbs
          (show 3 + q.2.order ≤ j + 3 by have := hP q List.mem_cons_self; omega)
        have hp := ih (fun r hr => hP r (List.mem_cons_of_mem q hr))
        change q.1.natAbs * (3 + q.2.order) +
            (P.map (fun r => r.1.natAbs * (3 + r.2.order))).sum ≤
          (j + 3) * (q.1.natAbs + markedTensorCoefficientMass P)
        calc
          _ ≤ q.1.natAbs * (j + 3) + (j + 3) * markedTensorCoefficientMass P :=
            Nat.add_le_add hq hp
          _ = _ := by ring
    exact hlist _ (fun q hq => (hinvariant j q hq).2)
  refine ⟨hinvariant j, hnext j, hbound j, ?_⟩
  induction j with
  | zero => norm_num [m63RicciArcExpression, markedTensorCoefficientMass]
  | succ j ih =>
    have h := (hbound j).trans (Nat.mul_le_mul_left (j + 3) ih)
    simpa only [Nat.add_assoc, Nat.factorial_succ] using h




theorem m63TangentRicci_arc_iterate [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ -> ℝ -> M)
    (hc : M62ShrinkingCurve F c) (j : Nat)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let f := fun y => m63UnmarkedTensorExpression F c D.ricciEvaluation
      (m63RicciArcExpression j) t y
    ((m62ArcDerivative F c t)^[j]) (m62TangentRicci F c t) x = f x ∧
      HasDerivAt f (curveSpeed F c t x *
        m63UnmarkedTensorExpression F c D.ricciEvaluation
          (m63RicciArcExpression (j + 1)) t x) x := by
  classical
  let D := F.connection t
  let K : Nat -> (z : ℝ × ℝ) -> TangentSpace (𝓡 n) (c z.1 z.2) := fun i z =>
    match i with
    | 0 => spatialUnitTangent F c z.2 z.1
    | r + 1 => m63CurvatureJet F c r z.2 z.1
  let ev := fun (A : MarkedTensorContraction 2) (y : ℝ) =>
    D.iteratedCovariantTensorDerivative D.ricciEvaluation A.order (c y t)
      (fun i => K (A.jet i) (y, t))
  have hK (i : Nat) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, K i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    cases i with
    | zero => exact unitTangent_joint_contMDiff F c hc
    | succ i => exact M63.curvatureJet_joint_contMDiff F c hc i
  have hKnext (i : Nat) (y : ℝ) :
      m62SpatialDerivative F c t (fun z => K i (z, t)) y = K (i + 1) (y, t) := by
    cases i <;> rfl
  have heval (A : MarkedTensorContraction 2) (i : Nat)
      (hi : A.jet A.test = i) (y : ℝ) :
      m63MarkedTensorTerm F c D.ricciEvaluation A t (fun z => K i (z, t)) y =
        ev A y := by
    apply congrArg (D.iteratedCovariantTensorDerivative D.ricciEvaluation A.order (c y t))
    funext z
    by_cases hz : z = A.test
    · subst z
      simp only [if_true, hi]
    · simp only [hz, if_false]
      rfl
  have hstored (A : MarkedTensorContraction 2) (B : MarkedTensorContraction 2)
      (hB : B ∈ A.derivativeBranches) : B.jet B.test = A.jet A.test := by
    rcases List.mem_cons.mp hB with rfl | hB
    · rfl
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hB
      have hine : A.test ≠ i := (Finset.mem_erase.mp (Finset.mem_toList.mp hi)).1.symm
      exact Function.update_of_ne hine _ _
  have htest (A : MarkedTensorContraction 2) (y : ℝ) :
      m63MarkedTensorTerm F c D.ricciEvaluation A t
        (fun z => K (A.jet A.test + 1) (z, t)) y = ev (A.slotStep A.test) y := by
    apply congrArg (D.iteratedCovariantTensorDerivative D.ricciEvaluation A.order (c y t))
    funext z
    by_cases hz : z = A.test
    · subst z
      simp only [MarkedTensorContraction.slotStep, Function.update_self, if_true]
    · simp only [MarkedTensorContraction.slotStep, Function.update_of_ne hz, hz, if_false]
      rfl
  have hterm (A : MarkedTensorContraction 2) (y : ℝ) :
      HasDerivAt (ev A)
        (curveSpeed F c t y *
          ((A.derivativeBranches.map (fun B => ev B y)).sum +
            ev (A.slotStep A.test) y)) y := by
    have hd := (m63HasDerivAt_markedTensorExpression F c hc D.ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation D) [(1, A)]
      (K (A.jet A.test)) (hK _) ht y).1
    simp only [m63MarkedTensorExpression, markedTensorExpressionDerivative,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.map_map, Function.comp_def,
      Int.cast_one, one_mul, add_zero] at hd
    have hfun : (fun z => m63MarkedTensorTerm F c D.ricciEvaluation A t
        (fun s => K (A.jet A.test) (s, t)) z) = ev A :=
      funext fun z => heval A _ rfl z
    rw [hfun] at hd
    apply hd.congr_deriv
    congr 1
    rw [show m62SpatialDerivative F c t (fun s => K (A.jet A.test) (s, t)) =
      (fun s => K (A.jet A.test + 1) (s, t)) from funext (hKnext _), htest]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro B hB
    exact heval B _ (hstored A B hB) y
  have hder (P : List (Int × MarkedTensorContraction 2)) (y : ℝ) :
      HasDerivAt (fun z => m63UnmarkedTensorExpression F c D.ricciEvaluation P t z)
        (curveSpeed F c t y *
          m63UnmarkedTensorExpression F c D.ricciEvaluation
            (markedTensorExpressionDerivative P ++
              P.map (fun q => (q.1, q.2.slotStep q.2.test))) t y) y := by
    have hrepeat (z : Int) (Q : List (MarkedTensorContraction 2)) :
        m63UnmarkedTensorExpression F c D.ricciEvaluation
          (Q.map (fun A => (z, A))) t y = (z : ℝ) * (Q.map (fun A => ev A y)).sum := by
      induction Q with
      | nil => simp [m63UnmarkedTensorExpression]
      | cons A Q ih =>
        change (z : ℝ) * ev A y + m63UnmarkedTensorExpression F c D.ricciEvaluation
          (Q.map (fun B => (z, B))) t y = _
        rw [ih]
        simp only [List.map_cons, List.sum_cons, mul_add]
    have happend (P Q : List (Int × MarkedTensorContraction 2)) :
        m63UnmarkedTensorExpression F c D.ricciEvaluation (P ++ Q) t y =
          m63UnmarkedTensorExpression F c D.ricciEvaluation P t y +
            m63UnmarkedTensorExpression F c D.ricciEvaluation Q t y := by
      simp only [m63UnmarkedTensorExpression, List.map_append, List.sum_append]
    induction P with
    | nil => simpa [m63UnmarkedTensorExpression, markedTensorExpressionDerivative] using
        hasDerivAt_const y (0 : ℝ)
    | cons q P ih =>
      have hd := ((hterm q.2 y).const_mul (q.1 : ℝ)).add ih
      apply hd.congr_deriv
      change _ = curveSpeed F c t y *
        m63UnmarkedTensorExpression F c D.ricciEvaluation
          ((q.2.derivativeBranches.map (fun A => (q.1, A)) ++
              markedTensorExpressionDerivative P) ++
            (q.1, q.2.slotStep q.2.test) :: P.map (fun r => (r.1, r.2.slotStep r.2.test))) t y
      simp only [happend]
      rw [hrepeat]
      change _ = curveSpeed F c t y *
        ((q.1 : ℝ) * (q.2.derivativeBranches.map (fun A => ev A y)).sum +
            m63UnmarkedTensorExpression F c D.ricciEvaluation
              (markedTensorExpressionDerivative P) t y +
          ((q.1 : ℝ) * ev (q.2.slotStep q.2.test) y +
            m63UnmarkedTensorExpression F c D.ricciEvaluation
              (P.map (fun r => (r.1, r.2.slotStep r.2.test))) t y))
      ring
  have hident (i : Nat) :
      ((m62ArcDerivative F c t)^[i]) (m62TangentRicci F c t) =
        fun y => m63UnmarkedTensorExpression F c D.ricciEvaluation
          (m63RicciArcExpression i) t y := by
    induction i with
    | zero =>
      funext y
      simp only [Function.iterate_zero_apply, m63RicciArcExpression,
        m63UnmarkedTensorExpression, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Int.cast_one, one_mul, add_zero,
        LeviCivitaData.iteratedCovariantTensorDerivative]
      rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      funext y
      rw [m62ArcDerivative, (hder (m63RicciArcExpression i) y).deriv]
      rw [← mul_assoc, inv_mul_cancel₀ (speed_pos F c hc (Ioo_subset_Icc_self ht) y).ne', one_mul]
      rfl
  exact ⟨congrFun (hident j) x, hder (m63RicciArcExpression j) x⟩

end PoincareConjecture
