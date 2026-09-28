import PoincareConjecture.Proofs.M04.TensorDerivativeClosure
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def pairedProduct {r : ℕ} (S T : CovariantTensorEvaluation n M r) :
    CovariantTensorEvaluation n M (r * 2) :=
  fun x w =>
    S x (fun i => w (finProdFinEquiv (i, (0 : Fin 2)))) *
      T x (fun i => w (finProdFinEquiv (i, (1 : Fin 2))))

private theorem paired_update_same {r : ℕ} {α : Type*}
    (w : Fin (r * 2) → α) (i : Fin r) (a : Fin 2) (v : α) :
    (fun j => Function.update w (finProdFinEquiv (i, a)) v
      (finProdFinEquiv (j, a))) =
      Function.update (fun j => w (finProdFinEquiv (j, a))) i v := by
  classical
  apply Function.update_comp_eq_of_injective'
  intro j k h
  exact congrArg Prod.fst (finProdFinEquiv.injective h)

private theorem paired_update_other {r : ℕ} {α : Type*}
    (w : Fin (r * 2) → α) (i : Fin r) (a b : Fin 2) (hab : a ≠ b) (v : α) :
    (fun j => Function.update w (finProdFinEquiv (i, a)) v
      (finProdFinEquiv (j, b))) = (fun j => w (finProdFinEquiv (j, b))) := by
  classical
  apply Function.update_comp_eq_of_forall_ne'
  intro j h
  exact hab (congrArg Prod.snd (finProdFinEquiv.injective h)).symm

omit [IsManifold (𝓡 n) ∞ M] in
private theorem pairedProduct_update_left {r : ℕ}
    (S T : CovariantTensorEvaluation n M r) (x : M)
    (w : Fin (r * 2) → TangentSpace (𝓡 n) x) (i : Fin r)
    (v : TangentSpace (𝓡 n) x) :
    pairedProduct S T x (Function.update w (finProdFinEquiv (i, (0 : Fin 2))) v) =
      S x (Function.update (fun j => w (finProdFinEquiv (j, (0 : Fin 2)))) i v) *
        T x (fun j => w (finProdFinEquiv (j, (1 : Fin 2)))) := by
  simp only [pairedProduct, paired_update_same,
    paired_update_other w i 0 1 (by decide) v]

omit [IsManifold (𝓡 n) ∞ M] in
private theorem pairedProduct_update_right {r : ℕ}
    (S T : CovariantTensorEvaluation n M r) (x : M)
    (w : Fin (r * 2) → TangentSpace (𝓡 n) x) (i : Fin r)
    (v : TangentSpace (𝓡 n) x) :
    pairedProduct S T x (Function.update w (finProdFinEquiv (i, (1 : Fin 2))) v) =
      S x (fun j => w (finProdFinEquiv (j, (0 : Fin 2)))) *
        T x (Function.update (fun j => w (finProdFinEquiv (j, (1 : Fin 2)))) i v) := by
  simp only [pairedProduct, paired_update_same,
    paired_update_other w i 1 0 (by decide) v]

theorem isSmoothCovariantTensor_pairedProduct {r : ℕ}
    {S T : CovariantTensorEvaluation n M r}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (pairedProduct S T) := by
  classical
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hS.1 x
    obtain ⟨B, hB⟩ := hT.1 x
    refine ⟨MultilinearMap.mk' (R := ℝ) (pairedProduct S T x) ?_ ?_, fun _ => rfl⟩
    · intro w j a b
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
      fin_cases k
      · change pairedProduct S T x (Function.update w (finProdFinEquiv (i, (0 : Fin 2))) (a + b)) =
          pairedProduct S T x (Function.update w (finProdFinEquiv (i, (0 : Fin 2))) a) +
            pairedProduct S T x (Function.update w (finProdFinEquiv (i, (0 : Fin 2))) b)
        simp only [pairedProduct_update_left, hA, A.map_update_add, add_mul]
      · change pairedProduct S T x (Function.update w (finProdFinEquiv (i, (1 : Fin 2))) (a + b)) =
          pairedProduct S T x (Function.update w (finProdFinEquiv (i, (1 : Fin 2))) a) +
            pairedProduct S T x (Function.update w (finProdFinEquiv (i, (1 : Fin 2))) b)
        simp only [pairedProduct_update_right, hB, B.map_update_add, mul_add]
    · intro w j c a
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
      fin_cases k
      · change pairedProduct S T x (Function.update w (finProdFinEquiv (i, (0 : Fin 2))) (c • a)) =
          c • pairedProduct S T x (Function.update w (finProdFinEquiv (i, (0 : Fin 2))) a)
        simp only [pairedProduct_update_left, hA, A.map_update_smul, smul_eq_mul]
        ring
      · change pairedProduct S T x (Function.update w (finProdFinEquiv (i, (1 : Fin 2))) (c • a)) =
          c • pairedProduct S T x (Function.update w (finProdFinEquiv (i, (1 : Fin 2))) a)
        simp only [pairedProduct_update_right, hB, B.map_update_smul, smul_eq_mul]
        ring
  · intro U hU X hX
    exact (hS.2 U hU (fun i => X (finProdFinEquiv (i, (0 : Fin 2))))
      (fun i => hX (finProdFinEquiv (i, (0 : Fin 2))))).mul
      (hT.2 U hU (fun i => X (finProdFinEquiv (i, (1 : Fin 2))))
        (fun i => hX (finProdFinEquiv (i, (1 : Fin 2)))))

private theorem paired_correction_sum {r : ℕ} {α : Type*}
    (S T : (Fin r → α) → ℝ) (w : Fin (r * 2) → α) (K : Fin (r * 2) → α) :
    (∑ j : Fin (r * 2),
      S (fun i => Function.update w j (K j) (finProdFinEquiv (i, (0 : Fin 2)))) *
        T (fun i => Function.update w j (K j) (finProdFinEquiv (i, (1 : Fin 2))))) =
      (∑ i : Fin r,
        S (Function.update (fun j => w (finProdFinEquiv (j, (0 : Fin 2)))) i
          (K (finProdFinEquiv (i, (0 : Fin 2)))))) *
        T (fun j => w (finProdFinEquiv (j, (1 : Fin 2)))) +
      S (fun j => w (finProdFinEquiv (j, (0 : Fin 2)))) *
        (∑ i : Fin r,
          T (Function.update (fun j => w (finProdFinEquiv (j, (1 : Fin 2)))) i
            (K (finProdFinEquiv (i, (1 : Fin 2)))))) := by
  classical
  let f (j : Fin (r * 2)) :=
    S (fun i => Function.update w j (K j) (finProdFinEquiv (i, (0 : Fin 2)))) *
      T (fun i => Function.update w j (K j) (finProdFinEquiv (i, (1 : Fin 2))))
  have h01 (i : Fin r) (v : α) := paired_update_other w i 0 1 (by decide) v
  have h10 (i : Fin r) (v : α) := paired_update_other w i 1 0 (by decide) v
  change (∑ j, f j) = _
  rw [← finProdFinEquiv.sum_comp f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, f, paired_update_same, h01, h10]
  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivative_pairedProduct (D : LeviCivitaData g) {r : ℕ}
    {S T : CovariantTensorEvaluation n M r}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (u : TangentSpace (𝓡 n) x)
    (w : Fin (r * 2) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (pairedProduct S T) x (Fin.cons u w) =
      D.covariantTensorDerivative S x
          (Fin.cons u (fun i => w (finProdFinEquiv (i, (0 : Fin 2))))) *
        T x (fun i => w (finProdFinEquiv (i, (1 : Fin 2)))) +
      S x (fun i => w (finProdFinEquiv (i, (0 : Fin 2)))) *
        D.covariantTensorDerivative T x
          (Fin.cons u (fun i => w (finProdFinEquiv (i, (1 : Fin 2))))) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let V (i : Fin (r * 2)) := FiberBundle.extend E (w i)
  let s := fun y => S y (fun i => V (finProdFinEquiv (i, (0 : Fin 2))) y)
  let t := fun y => T y (fun i => V (finProdFinEquiv (i, (1 : Fin 2))) y)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hV (i : Fin (r * 2)) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (V i)) e.baseSet :=
    contMDiffOn_extend_baseSet (w i)
  have hs : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) s x :=
    ((hS.2 e.baseSet e.open_baseSet (fun i => V (finProdFinEquiv (i, (0 : Fin 2))))
      (fun i => hV (finProdFinEquiv (i, (0 : Fin 2))))).contMDiffAt
        (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have ht : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) t x :=
    ((hT.2 e.baseSet e.open_baseSet (fun i => V (finProdFinEquiv (i, (1 : Fin 2))))
      (fun i => hV (finProdFinEquiv (i, (1 : Fin 2))))).contMDiffAt
        (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hd : mvfderiv (𝓡 n) (fun y => pairedProduct S T y (fun i => V i y)) x u =
      S x (fun i => w (finProdFinEquiv (i, (0 : Fin 2)))) *
          mvfderiv (𝓡 n) t x u +
        T x (fun i => w (finProdFinEquiv (i, (1 : Fin 2)))) *
          mvfderiv (𝓡 n) s x u := by
    have h := congrArg (fun L => L u) (mvfderiv_fun_mul hs ht)
    simpa only [pairedProduct, s, t, V, add_apply,
      smul_apply, smul_eq_mul, FiberBundle.extend_apply_self] using h
  simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ]
  change mvfderiv (𝓡 n) (fun y => pairedProduct S T y (fun i => V i y)) x u -
      (∑ j, pairedProduct S T x
        (Function.update w j (D.connection (V j) x u))) = _
  rw [hd]
  have hc := paired_correction_sum (S x) (T x) w (fun j => D.connection (V j) x u)
  change (∑ j, pairedProduct S T x
    (Function.update w j (D.connection (V j) x u))) = _ at hc
  rw [hc]
  dsimp only [s, t, V]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_derivative (D : LeviCivitaData g) {r : ℕ}
    {T : CovariantTensorEvaluation n M r} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {A : (y : M) → TangentSpace (𝓡 n) y}
    {V : Fin r → (y : M) → TangentSpace (𝓡 n) y}
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U)
    (hV : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (V i)) U) {x : M} (hx : x ∈ U) :
    mvfderiv (𝓡 n) (fun y => T y (fun i => V i y)) x (A x) =
      D.covariantTensorDerivative T x (Fin.cons (A x) (fun i => V i x)) +
        ∑ i, T x (Function.update (fun j => V j x) i (D.connection (V i) x (A x))) := by
  let AV : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y := Fin.cons A V
  have hAV (i : Fin (r + 1)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (AV i)) U := by
    cases i using Fin.cases with
    | zero => exact hA
    | succ j => exact hV j
  have h := covariantTensorDerivativeOnFields_eq D hT hU hAV hx
  have he : (fun i => AV i x) = Fin.cons (A x) (fun i => V i x) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [he] at h
  simp only [covariantTensorDerivativeOnFields, AV, Fin.cons_zero, Fin.cons_succ] at h
  exact sub_eq_iff_eq_add.mp h

set_option backward.isDefEq.respectTransparency false in
private theorem derivative_evaluation_derivative (D : LeviCivitaData g) {r : ℕ}
    {T : CovariantTensorEvaluation n M r} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {A B : (y : M) → TangentSpace (𝓡 n) y}
    {V : Fin r → (y : M) → TangentSpace (𝓡 n) y}
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% B) U)
    (hV : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (V i)) U) {x : M} (hx : x ∈ U) :
    mvfderiv (𝓡 n) (fun y => D.covariantTensorDerivative T y
      (Fin.cons (B y) (fun i => V i y))) x (A x) =
      D.iteratedCovariantTensorDerivative T 2 x
          (Fin.cons (A x) (Fin.cons (B x) (fun i => V i x))) +
        D.covariantTensorDerivative T x
          (Fin.cons (D.connection B x (A x)) (fun i => V i x)) +
        ∑ i, D.covariantTensorDerivative T x
          (Fin.cons (B x)
            (Function.update (fun j => V j x) i (D.connection (V i) x (A x)))) := by
  let BV : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y := Fin.cons B V
  have hBV (i : Fin (r + 1)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (BV i)) U := by
    cases i using Fin.cases with
    | zero => exact hB
    | succ j => exact hV j
  have h := evaluation_derivative D
    (isSmoothCovariantTensor_covariantTensorDerivative D hT) hU hA hBV hx
  have he (y : M) : (fun i => BV i y) = Fin.cons (B y) (fun i => V i y) := by
    funext i
    cases i using Fin.cases <;> rfl
  simp only [he, Fin.sum_univ_succ, BV, Fin.cons_zero, Fin.cons_succ,
    Fin.update_cons_zero, ← Fin.cons_update] at h
  simpa only [LeviCivitaData.iteratedCovariantTensorDerivative, add_assoc] using h

set_option maxHeartbeats 1500000 in

set_option backward.isDefEq.respectTransparency false in
theorem second_covariantTensorDerivative_pairedProduct (D : LeviCivitaData g) {r : ℕ}
    {S T : CovariantTensorEvaluation n M r}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (u v : TangentSpace (𝓡 n) x)
    (w : Fin (r * 2) → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (pairedProduct S T) 2 x
        (Fin.cons u (Fin.cons v w)) =
      D.iteratedCovariantTensorDerivative S 2 x
          (Fin.cons u (Fin.cons v
            (fun i => w (finProdFinEquiv (i, (0 : Fin 2)))))) *
        T x (fun i => w (finProdFinEquiv (i, (1 : Fin 2)))) +
      D.covariantTensorDerivative S x
          (Fin.cons v (fun i => w (finProdFinEquiv (i, (0 : Fin 2))))) *
        D.covariantTensorDerivative T x
          (Fin.cons u (fun i => w (finProdFinEquiv (i, (1 : Fin 2))))) +
      D.covariantTensorDerivative S x
          (Fin.cons u (fun i => w (finProdFinEquiv (i, (0 : Fin 2))))) *
        D.covariantTensorDerivative T x
          (Fin.cons v (fun i => w (finProdFinEquiv (i, (1 : Fin 2))))) +
      S x (fun i => w (finProdFinEquiv (i, (0 : Fin 2)))) *
        D.iteratedCovariantTensorDerivative T 2 x
          (Fin.cons u (Fin.cons v
            (fun i => w (finProdFinEquiv (i, (1 : Fin 2)))))) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let A := FiberBundle.extend E u
  let B := FiberBundle.extend E v
  let V (i : Fin (r * 2)) := FiberBundle.extend E (w i)
  let V0 (i : Fin r) := V (finProdFinEquiv (i, (0 : Fin 2)))
  let V1 (i : Fin r) := V (finProdFinEquiv (i, (1 : Fin 2)))
  let even : Fin r → TangentSpace (𝓡 n) x :=
    fun i => w (finProdFinEquiv (i, (0 : Fin 2)))
  let odd : Fin r → TangentSpace (𝓡 n) x :=
    fun i => w (finProdFinEquiv (i, (1 : Fin 2)))
  let s := fun y => S y (fun i => V0 i y)
  let t := fun y => T y (fun i => V1 i y)
  let ds := fun y => D.covariantTensorDerivative S y (Fin.cons (B y) (fun i => V0 i y))
  let dt := fun y => D.covariantTensorDerivative T y (Fin.cons (B y) (fun i => V1 i y))
  let K (i : Fin (r * 2)) := D.connection (V i) x u
  let KB := D.connection B x u
  let cs := ∑ i : Fin r, S x (Function.update even i (K (finProdFinEquiv (i, (0 : Fin 2)))))
  let ct := ∑ i : Fin r, T x (Function.update odd i (K (finProdFinEquiv (i, (1 : Fin 2)))))
  let cds := ∑ i : Fin r, D.covariantTensorDerivative S x
    (Fin.cons v (Function.update even i (K (finProdFinEquiv (i, (0 : Fin 2))))))
  let cdt := ∑ i : Fin r, D.covariantTensorDerivative T x
    (Fin.cons v (Function.update odd i (K (finProdFinEquiv (i, (1 : Fin 2))))))
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% A) e.baseSet :=
    contMDiffOn_extend_baseSet u
  have hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% B) e.baseSet :=
    contMDiffOn_extend_baseSet v
  have hV (i : Fin (r * 2)) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (V i)) e.baseSet :=
    contMDiffOn_extend_baseSet (w i)
  have hV0 (i : Fin r) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (V0 i)) e.baseSet :=
    hV (finProdFinEquiv (i, (0 : Fin 2)))
  have hV1 (i : Fin r) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (V1 i)) e.baseSet :=
    hV (finProdFinEquiv (i, (1 : Fin 2)))
  let BV0 : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y := Fin.cons B V0
  let BV1 : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y := Fin.cons B V1
  have hBV0 (i : Fin (r + 1)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (BV0 i)) e.baseSet := by
    cases i using Fin.cases with
    | zero => exact hB
    | succ j => exact hV0 j
  have hBV1 (i : Fin (r + 1)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (BV1 i)) e.baseSet := by
    cases i using Fin.cases with
    | zero => exact hB
    | succ j => exact hV1 j
  have hsSmooth : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ s e.baseSet :=
    hS.2 e.baseSet e.open_baseSet V0 hV0
  have htSmooth : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ t e.baseSet :=
    hT.2 e.baseSet e.open_baseSet V1 hV1
  have hdsSmooth : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ds e.baseSet := by
    apply ((isSmoothCovariantTensor_covariantTensorDerivative D hS).2
      e.baseSet e.open_baseSet BV0 hBV0).congr
    intro y hy
    apply congrArg (D.covariantTensorDerivative S y)
    funext i
    cases i using Fin.cases <;> rfl
  have hdtSmooth : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ dt e.baseSet := by
    apply ((isSmoothCovariantTensor_covariantTensorDerivative D hT).2
      e.baseSet e.open_baseSet BV1 hBV1).congr
    intro y hy
    apply congrArg (D.covariantTensorDerivative T y)
    funext i
    cases i using Fin.cases <;> rfl
  have hs : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) s x :=
    (hsSmooth.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have ht : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) t x :=
    (htSmooth.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hds : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) ds x :=
    (hdsSmooth.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdt : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) dt x :=
    (hdtSmooth.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hsPoint : s x = S x even := by simp only [s, V0, V, even, FiberBundle.extend_apply_self]
  have htPoint : t x = T x odd := by simp only [t, V1, V, odd, FiberBundle.extend_apply_self]
  have hdsPoint : ds x = D.covariantTensorDerivative S x (Fin.cons v even) := by
    simp only [ds, B, V0, V, even, FiberBundle.extend_apply_self]
  have hdtPoint : dt x = D.covariantTensorDerivative T x (Fin.cons v odd) := by
    simp only [dt, B, V1, V, odd, FiberBundle.extend_apply_self]
  have hsDir : mvfderiv (𝓡 n) s x u =
      D.covariantTensorDerivative S x (Fin.cons u even) + cs := by
    simpa only [s, A, V0, V, even, K, cs, FiberBundle.extend_apply_self] using
      evaluation_derivative D hS e.open_baseSet hA hV0 hx
  have htDir : mvfderiv (𝓡 n) t x u =
      D.covariantTensorDerivative T x (Fin.cons u odd) + ct := by
    simpa only [t, A, V1, V, odd, K, ct, FiberBundle.extend_apply_self] using
      evaluation_derivative D hT e.open_baseSet hA hV1 hx
  have hdsDir : mvfderiv (𝓡 n) ds x u =
      D.iteratedCovariantTensorDerivative S 2 x (Fin.cons u (Fin.cons v even)) +
        D.covariantTensorDerivative S x (Fin.cons KB even) + cds := by
    simpa only [ds, A, B, V0, V, even, KB, K, cds, FiberBundle.extend_apply_self] using
      derivative_evaluation_derivative D hS e.open_baseSet hA hB hV0 hx
  have hdtDir : mvfderiv (𝓡 n) dt x u =
      D.iteratedCovariantTensorDerivative T 2 x (Fin.cons u (Fin.cons v odd)) +
        D.covariantTensorDerivative T x (Fin.cons KB odd) + cdt := by
    simpa only [dt, A, B, V1, V, odd, KB, K, cdt, FiberBundle.extend_apply_self] using
      derivative_evaluation_derivative D hT e.open_baseSet hA hB hV1 hx
  have hformula :
      (fun y => D.covariantTensorDerivative (pairedProduct S T) y
        (Fin.cons (B y) (fun i => V i y))) =
      (fun y => ds y * t y + s y * dt y) := by
    funext y
    exact covariantTensorDerivative_pairedProduct D hS hT y (B y) (fun i => V i y)
  have hprodDir :
      mvfderiv (𝓡 n) (fun y => D.covariantTensorDerivative (pairedProduct S T) y
        (Fin.cons (B y) (fun i => V i y))) x u =
      mvfderiv (𝓡 n) ds x u * t x + ds x * mvfderiv (𝓡 n) t x u +
        mvfderiv (𝓡 n) s x u * dt x + s x * mvfderiv (𝓡 n) dt x u := by
    rw [hformula]
    change mvfderiv (𝓡 n) (ds * t + s * dt) x u = _
    rw [mvfderiv_add (hds.mul ht) (hs.mul hdt),
      mvfderiv_mul hds ht, mvfderiv_mul hs hdt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hsPoint, htPoint, hdsPoint, hdtPoint, hsDir, htDir, hdsDir, hdtDir] at hprodDir
  have hcorr :
      (∑ j : Fin (r * 2), D.covariantTensorDerivative (pairedProduct S T) x
        (Fin.cons v (Function.update w j (K j)))) =
      (cds * T x odd + D.covariantTensorDerivative S x (Fin.cons v even) * ct) +
        (cs * D.covariantTensorDerivative T x (Fin.cons v odd) + S x even * cdt) := by
    simp_rw [covariantTensorDerivative_pairedProduct D hS hT]
    rw [Finset.sum_add_distrib]
    have h1 := paired_correction_sum
      (fun z => D.covariantTensorDerivative S x (Fin.cons v z)) (T x) w K
    have h2 := paired_correction_sum
      (S x) (fun z => D.covariantTensorDerivative T x (Fin.cons v z)) w K
    exact congrArg₂ (fun a b : ℝ => a + b) h1 h2
  have hprodCov :
      mvfderiv (𝓡 n) (fun y => D.covariantTensorDerivative (pairedProduct S T) y
        (Fin.cons (B y) (fun i => V i y))) x u =
      D.iteratedCovariantTensorDerivative (pairedProduct S T) 2 x
          (Fin.cons u (Fin.cons v w)) +
        D.covariantTensorDerivative (pairedProduct S T) x (Fin.cons KB w) +
        ∑ j, D.covariantTensorDerivative (pairedProduct S T) x
          (Fin.cons v (Function.update w j (K j))) := by
    simpa only [A, B, V, KB, K, FiberBundle.extend_apply_self] using
      derivative_evaluation_derivative D (isSmoothCovariantTensor_pairedProduct hS hT)
        e.open_baseSet hA hB hV hx
  have hKB := covariantTensorDerivative_pairedProduct D hS hT x KB w
  rw [hKB, hcorr] at hprodCov
  linear_combination hprodDir - hprodCov

end PoincareConjecture.M04
