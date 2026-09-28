import PoincareConjecture.Proofs.M04.RiemannRegularity
import PoincareConjecture.Proofs.M04.TensorMetricTrace
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private def curvatureRightSlots {i j r : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin r) :
    (Fin (4+i) ⊕ Fin (4+(j+1))) ≃ Fin (r+1) :=
  (((Equiv.refl (Fin (4+i))).sumCongr
      ((finSuccEquiv (4+j)).trans
        (Equiv.optionEquivSumPUnit.{0, 0} (Fin (4+j))))).trans
      (Equiv.sumAssoc (Fin (4+i)) (Fin (4+j)) PUnit.{1}).symm).trans
    ((σ.sumCongr (Equiv.refl PUnit.{1})).trans
      ((finSuccEquiv r).trans (Equiv.optionEquivSumPUnit.{0, 0} (Fin r))).symm)

private def curvatureLeftSlots {i j r : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin r) :
    (Fin (4+(i+1)) ⊕ Fin (4+j)) ≃ Fin (r+1) :=
  (Equiv.sumComm (Fin (4+(i+1))) (Fin (4+j))).trans
    (curvatureRightSlots (i := j) (j := i)
      ((Equiv.sumComm (Fin (4+j)) (Fin (4+i))).trans σ))

private noncomputable def curvaturePairProduct (D : LeviCivitaData g)
    (i j : ℕ) {r : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin r) :
    CovariantTensorEvaluation n M r :=
  fun x v ↦
    D.iteratedCovariantTensorDerivative D.riemannEvaluation i x
      (fun a ↦ v (σ (Sum.inl a))) *
    D.iteratedCovariantTensorDerivative D.riemannEvaluation j x
      (fun b ↦ v (σ (Sum.inr b)))

set_option backward.isDefEq.respectTransparency false in
private theorem isSmoothCovariantTensor_curvaturePairProduct
    (D : LeviCivitaData g) (i j : ℕ) {r : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin r) :
    IsSmoothCovariantTensor (curvaturePairProduct D i j σ) := by
  have hs (m : ℕ) : IsSmoothCovariantTensor
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) := by
    induction m with
    | zero => exact isSmoothCovariantTensor_riemannEvaluation D
    | succ m ih => exact isSmoothCovariantTensor_covariantTensorDerivative D ih
  constructor
  · intro x
    obtain ⟨A, hA⟩ := (hs i).1 x
    obtain ⟨B, hB⟩ := (hs j).1 x
    refine ⟨((TensorProduct.lid ℝ ℝ).toLinearMap.compMultilinearMap
      (A.domCoprod B)).domDomCongr σ, ?_⟩
    intro v
    change _ = (TensorProduct.lid ℝ ℝ)
      (TensorProduct.tmul ℝ (A (fun a ↦ v (σ (Sum.inl a))))
        (B (fun b ↦ v (σ (Sum.inr b)))))
    simp only [TensorProduct.lid_tmul, smul_eq_mul, curvaturePairProduct, hA, hB]
  · intro V hV X hX
    exact ((hs i).2 V hV (fun a ↦ X (σ (Sum.inl a)))
      (fun a ↦ hX (σ (Sum.inl a)))).mul
      ((hs j).2 V hV (fun b ↦ X (σ (Sum.inr b)))
        (fun b ↦ hX (σ (Sum.inr b))))

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem covariantTensorDerivative_curvaturePairProduct
    (D : LeviCivitaData g) (i j : ℕ) {r : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin r)
    (x : M) (v : Fin (r + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (curvaturePairProduct D i j σ) x v =
      curvaturePairProduct D (i+1) j (curvatureLeftSlots σ) x v +
      curvaturePairProduct D i (j+1) (curvatureRightSlots σ) x v := by
  classical
  let u := v 0
  let w : Fin r → TangentSpace (𝓡 n) x := fun a ↦ v a.succ
  have hv : Fin.cons u w = v := by
    funext a
    cases a using Fin.cases <;> rfl
  rw [← hv]
  let S := D.iteratedCovariantTensorDerivative D.riemannEvaluation i
  let T := D.iteratedCovariantTensorDerivative D.riemannEvaluation j
  have hs (m : ℕ) : IsSmoothCovariantTensor
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) := by
    induction m with
    | zero => exact isSmoothCovariantTensor_riemannEvaluation D
    | succ m ih => exact isSmoothCovariantTensor_covariantTensorDerivative D ih
  have hLl : (fun a : Fin (4+(i+1)) ↦
      (Fin.cons u w : Fin (r+1) → TangentSpace (𝓡 n) x)
        (curvatureLeftSlots σ (Sum.inl a))) =
      (Fin.cons u (fun a : Fin (4+i) ↦ w (σ (Sum.inl a))) :
        Fin (4+(i+1)) → TangentSpace (𝓡 n) x) := by
    funext a
    cases a using Fin.cases <;>
      simp [curvatureLeftSlots, curvatureRightSlots, Equiv.sumCongr]
  have hLr : (fun b : Fin (4+j) ↦
      (Fin.cons u w : Fin (r+1) → TangentSpace (𝓡 n) x)
        (curvatureLeftSlots σ (Sum.inr b))) =
      (fun b ↦ w (σ (Sum.inr b))) := by
    funext b
    simp [curvatureLeftSlots, curvatureRightSlots, Equiv.sumCongr]
  have hRl : (fun a : Fin (4+i) ↦
      (Fin.cons u w : Fin (r+1) → TangentSpace (𝓡 n) x)
        (curvatureRightSlots σ (Sum.inl a))) =
      (fun a ↦ w (σ (Sum.inl a))) := by
    funext a
    simp [curvatureRightSlots, Equiv.sumCongr]
  have hRr : (fun b : Fin (4+(j+1)) ↦
      (Fin.cons u w : Fin (r+1) → TangentSpace (𝓡 n) x)
        (curvatureRightSlots σ (Sum.inr b))) =
      (Fin.cons u (fun b : Fin (4+j) ↦ w (σ (Sum.inr b))) :
        Fin (4+(j+1)) → TangentSpace (𝓡 n) x) := by
    funext b
    cases b using Fin.cases <;> simp [curvatureRightSlots, Equiv.sumCongr]
  conv_rhs => simp only [curvaturePairProduct, hLl, hLr, hRl, hRr]
  change D.covariantTensorDerivative (curvaturePairProduct D i j σ) x
      (Fin.cons u w) =
    D.covariantTensorDerivative S x (Fin.cons u (fun a ↦ w (σ (Sum.inl a)))) *
      T x (fun b ↦ w (σ (Sum.inr b))) +
    S x (fun a ↦ w (σ (Sum.inl a))) *
      D.covariantTensorDerivative T x (Fin.cons u (fun b ↦ w (σ (Sum.inr b))))
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let W (a : Fin r) := FiberBundle.extend E (w a)
  let s := fun y ↦ S y (fun a ↦ W (σ (Sum.inl a)) y)
  let t := fun y ↦ T y (fun b ↦ W (σ (Sum.inr b)) y)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hW (a : Fin r) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E))
      ∞ (T% (W a)) e.baseSet := contMDiffOn_extend_baseSet (w a)
  have hsd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) s x :=
    (((hs i).2 e.baseSet e.open_baseSet (fun a ↦ W (σ (Sum.inl a)))
      (fun a ↦ hW (σ (Sum.inl a)))).contMDiffAt
        (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have htd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) t x :=
    (((hs j).2 e.baseSet e.open_baseSet (fun b ↦ W (σ (Sum.inr b)))
      (fun b ↦ hW (σ (Sum.inr b)))).contMDiffAt
        (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hd : mvfderiv (𝓡 n)
      (fun y ↦ curvaturePairProduct D i j σ y (fun a ↦ W a y)) x u =
      S x (fun a ↦ w (σ (Sum.inl a))) * mvfderiv (𝓡 n) t x u +
      T x (fun b ↦ w (σ (Sum.inr b))) * mvfderiv (𝓡 n) s x u := by
    have he := congrArg (fun A ↦ A u) (mvfderiv_fun_mul hsd htd)
    simpa only [s, t, W, S, T, curvaturePairProduct, add_apply, smul_apply,
      smul_eq_mul, FiberBundle.extend_apply_self] using he
  let c := fun a ↦ D.connection (W a) x u
  have hleft (a : Fin (4+i)) :
      curvaturePairProduct D i j σ x (Function.update w (σ (Sum.inl a))
        (c (σ (Sum.inl a)))) =
      S x (Function.update (fun b ↦ w (σ (Sum.inl b))) a (c (σ (Sum.inl a)))) *
        T x (fun b ↦ w (σ (Sum.inr b))) := by
    simp only [curvaturePairProduct, Function.update_apply_equiv_apply,
      Equiv.symm_apply_apply, Sum.update_inl_apply_inl, Sum.update_inl_apply_inr,
      Function.comp_def, S, T]
  have hright (b : Fin (4+j)) :
      curvaturePairProduct D i j σ x (Function.update w (σ (Sum.inr b))
        (c (σ (Sum.inr b)))) =
      S x (fun a ↦ w (σ (Sum.inl a))) *
        T x (Function.update (fun a ↦ w (σ (Sum.inr a))) b (c (σ (Sum.inr b)))) := by
    simp only [curvaturePairProduct, Function.update_apply_equiv_apply,
      Equiv.symm_apply_apply, Sum.update_inr_apply_inl, Sum.update_inr_apply_inr,
      Function.comp_def, S, T]
  have hc : (∑ a, curvaturePairProduct D i j σ x (Function.update w a (c a))) =
      (∑ a, S x (Function.update (fun b ↦ w (σ (Sum.inl b))) a
        (c (σ (Sum.inl a))))) * T x (fun b ↦ w (σ (Sum.inr b))) +
      S x (fun a ↦ w (σ (Sum.inl a))) *
        (∑ b, T x (Function.update (fun a ↦ w (σ (Sum.inr a))) b
          (c (σ (Sum.inr b))))) := by
    rw [← σ.sum_comp (fun a ↦ curvaturePairProduct D i j σ x
      (Function.update w a (c a))), Fintype.sum_sum_type]
    simp only [hleft, hright, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ]
  change mvfderiv (𝓡 n)
    (fun y ↦ curvaturePairProduct D i j σ y (fun a ↦ W a y)) x u -
      (∑ a, curvaturePairProduct D i j σ x (Function.update w a (c a))) = _
  rw [hd, hc]
  dsimp only [s, t, c, W]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem tensorNorm_curvaturePairProduct (D : LeviCivitaData g)
    (i j : ℕ) {r : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin r) (x : M) :
    g.tensorNorm (curvaturePairProduct D i j σ) x =
      D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm j x := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let S := fun a : Fin (4+i) → Fin d ↦
    D.iteratedCovariantTensorDerivative D.riemannEvaluation i x (fun z ↦ b (a z))
  let T := fun a : Fin (4+j) → Fin d ↦
    D.iteratedCovariantTensorDerivative D.riemannEvaluation j x (fun z ↦ b (a z))
  let e : (Fin r → Fin d) ≃ (Fin (4+i) → Fin d) × (Fin (4+j) → Fin d) :=
    (Equiv.arrowCongr σ.symm (Equiv.refl (Fin d))).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  have hsum : (∑ a : Fin r → Fin d,
      (curvaturePairProduct D i j σ x (fun z ↦ b (a z))) ^ 2) =
      (∑ a, (S a) ^ 2) * ∑ a, (T a) ^ 2 := by
    calc
      _ = ∑ a : Fin r → Fin d, (S (e a).1) ^ 2 * (T (e a).2) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        exact mul_pow _ _ 2
      _ = ∑ p : (Fin (4+i) → Fin d) × (Fin (4+j) → Fin d),
          (S p.1) ^ 2 * (T p.2) ^ 2 :=
        e.sum_comp (fun p : (Fin (4+i) → Fin d) × (Fin (4+j) → Fin d) ↦
          (S p.1) ^ 2 * (T p.2) ^ 2)
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
  change Real.sqrt (∑ a : Fin r → Fin d,
    (curvaturePairProduct D i j σ x (fun z ↦ b (a z))) ^ 2) =
      Real.sqrt (∑ a, (S a) ^ 2) * Real.sqrt (∑ a, (T a) ^ 2)
  rw [hsum, Real.sqrt_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

noncomputable def curvaturePairContraction (D : LeviCivitaData g)
    (i j : ℕ) {k : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin (k + 4)) :
    CovariantTensorEvaluation n M k :=
  fun x v ↦
    let b := g.orthonormalBasis x
    ∑ p, ∑ q,
      (let W := Fin.append v ![b p, b p, b q, b q]
       D.iteratedCovariantTensorDerivative D.riemannEvaluation i x
         (fun a ↦ W (σ (Sum.inl a))) *
       D.iteratedCovariantTensorDerivative D.riemannEvaluation j x
         (fun c ↦ W (σ (Sum.inr c))))

private theorem curvaturePairContraction_eq_doubleTrace
    (D : LeviCivitaData g) (i j : ℕ) {k : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin (k + 4)) :
    curvaturePairContraction D i j σ =
      tensorTraceLast g (tensorTraceLast g (curvaturePairProduct D i j σ)) := by
  funext x v
  have ha (p q : TangentSpace (𝓡 n) x) :
      Fin.append (Fin.append v ![p, p]) ![q, q] =
        Fin.append v ![p, p, q, q] := by
    have ht : Fin.append ![p, p] ![q, q] = ![p, p, q, q] := by
      funext a
      fin_cases a <;> rfl
    rw [Fin.append_assoc, ht]
    funext a
    rfl
  simp only [curvaturePairContraction, tensorTraceLast, curvaturePairProduct, ha]

set_option backward.isDefEq.respectTransparency false in
private theorem covariantTensorDerivative_curvaturePairContraction_exact
    (D : LeviCivitaData g) (i j : ℕ) {k : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin (k + 4))
    (x : M) (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (curvaturePairContraction D i j σ) x v =
      curvaturePairContraction D (i+1) j (curvatureLeftSlots σ) x v +
      curvaturePairContraction D i (j+1) (curvatureRightSlots σ) x v := by
  have hP := isSmoothCovariantTensor_curvaturePairProduct D i j σ
  have hder : D.covariantTensorDerivative (curvaturePairProduct D i j σ) =
      (fun y w ↦ curvaturePairProduct D (i+1) j (curvatureLeftSlots σ) y w +
        curvaturePairProduct D i (j+1) (curvatureRightSlots σ) y w) := by
    funext y w
    exact covariantTensorDerivative_curvaturePairProduct D i j σ y w
  rw [curvaturePairContraction_eq_doubleTrace,
    covariantTensorDerivative_tensorTraceLast D
      (isSmoothCovariantTensor_tensorTraceLast g hP)]
  have ht : D.covariantTensorDerivative (tensorTraceLast g
      (curvaturePairProduct D i j σ)) =
      tensorTraceLast g (D.covariantTensorDerivative (curvaturePairProduct D i j σ)) := by
    funext y w
    exact covariantTensorDerivative_tensorTraceLast D hP y w
  rw [ht, hder, curvaturePairContraction_eq_doubleTrace,
    curvaturePairContraction_eq_doubleTrace]
  simp only [tensorTraceLast, Finset.sum_add_distrib]

theorem isSmoothCovariantTensor_curvaturePairContraction
    (D : LeviCivitaData g) (i j : ℕ) {k : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin (k + 4)) :
    IsSmoothCovariantTensor (curvaturePairContraction D i j σ) := by
  rw [curvaturePairContraction_eq_doubleTrace]
  exact isSmoothCovariantTensor_tensorTraceLast g
    (isSmoothCovariantTensor_tensorTraceLast g
      (isSmoothCovariantTensor_curvaturePairProduct D i j σ))

theorem exists_curvaturePairContraction_derivative_slots
    (D : LeviCivitaData g) (i j : ℕ) {k : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin (k + 4)) :
    ∃ σL : (Fin (4+(i+1)) ⊕ Fin (4+j)) ≃ Fin ((k+1)+4),
    ∃ σR : (Fin (4+i) ⊕ Fin (4+(j+1))) ≃ Fin ((k+1)+4),
      D.covariantTensorDerivative (curvaturePairContraction D i j σ) =
        fun x v ↦ curvaturePairContraction D (i+1) j σL x v +
          curvaturePairContraction D i (j+1) σR x v := by
  refine ⟨curvatureLeftSlots σ, curvatureRightSlots σ, ?_⟩
  funext x v
  exact covariantTensorDerivative_curvaturePairContraction_exact D i j σ x v

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem tensorNorm_curvaturePairContraction_le (D : LeviCivitaData g)
    (i j : ℕ) {k : ℕ}
    (σ : (Fin (4 + i) ⊕ Fin (4 + j)) ≃ Fin (k + 4)) (x : M) :
    g.tensorNorm (curvaturePairContraction D i j σ) x ≤
      (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm j x := by
  classical
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let P := curvaturePairProduct D i j σ
  let C := curvaturePairContraction D i j σ
  let diag : (Fin k → Fin d) × (Fin d × Fin d) → (Fin (k+4) → Fin d) :=
    fun z ↦ Fin.append z.1 ![z.2.1, z.2.1, z.2.2, z.2.2]
  let f := fun a : Fin (k+4) → Fin d ↦ (P x (fun z ↦ b (a z))) ^ 2
  have hf (a : Fin (k+4) → Fin d) : 0 ≤ f a := sq_nonneg _
  have hdiag (a : Fin k → Fin d) (p q : Fin d) :
      (fun z ↦ b (diag (a, p, q) z)) =
        Fin.append (fun z ↦ b (a z)) ![b p, b p, b q, b q] := by
    funext z
    refine Fin.addCases ?_ ?_ z
    · intro s
      simp only [diag, Fin.append_left]
    · intro s
      simp only [diag, Fin.append_right]
      fin_cases s <;> rfl
  have hinj : Function.Injective diag := by
    rintro ⟨a, p, q⟩ ⟨a', p', q'⟩ he
    have ha : a = a' := by
      funext s
      simpa only [diag, Fin.append_left] using congrFun he (Fin.castAdd 4 s)
    have hp : p = p' := by
      simpa only [diag, Fin.append_right, Matrix.cons_val_zero] using
        congrFun he (Fin.natAdd k (0 : Fin 4))
    have hq : q = q' := by
      simpa only [diag, Fin.append_right, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] using
        congrFun he (Fin.natAdd k (2 : Fin 4))
    exact Prod.ext ha (Prod.ext hp hq)
  have hpoint (a : Fin k → Fin d) :
      (C x (fun z ↦ b (a z))) ^ 2 ≤
        (d : ℝ) ^ 2 * ∑ pq : Fin d × Fin d, f (diag (a, pq)) := by
    have he : C x (fun z ↦ b (a z)) =
        ∑ pq : Fin d × Fin d, P x (fun z ↦ b (diag (a, pq) z)) := by
      rw [Fintype.sum_prod_type]
      simp only [hdiag, C, P, curvaturePairContraction, curvaturePairProduct, b]
      rfl
    rw [he]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin d × Fin d ↦ (1 : ℝ))
      (fun pq ↦ P x (fun z ↦ b (diag (a, pq) z)))
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Nat.cast_mul, pow_two, f] using hcs
  have hsel : (∑ a : Fin k → Fin d, ∑ pq : Fin d × Fin d,
      f (diag (a, pq))) ≤ ∑ a : Fin (k+4) → Fin d, f a := by
    calc
      _ = ∑ z : (Fin k → Fin d) × (Fin d × Fin d), f (diag z) :=
        (Fintype.sum_prod_type _).symm
      _ = ∑ a ∈ Finset.univ.image diag, f a := by
        rw [Finset.sum_image (fun a _ b _ h ↦ hinj h)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ ↦ hf a)
  have hsquares : (∑ a : Fin k → Fin d, (C x (fun z ↦ b (a z))) ^ 2) ≤
      (d : ℝ) ^ 2 * ∑ a : Fin (k+4) → Fin d, f a := by
    calc
      _ ≤ ∑ a : Fin k → Fin d, (d : ℝ) ^ 2 *
          ∑ pq : Fin d × Fin d, f (diag (a, pq)) :=
        Finset.sum_le_sum fun a _ ↦ hpoint a
      _ = (d : ℝ) ^ 2 *
          (∑ a : Fin k → Fin d, ∑ pq : Fin d × Fin d, f (diag (a, pq))) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsel (sq_nonneg _)
  have hnorm : g.tensorNorm C x ≤ (d : ℝ) * g.tensorNorm P x := by
    change Real.sqrt (∑ a : Fin k → Fin d, (C x (fun z ↦ b (a z))) ^ 2) ≤
      (d : ℝ) * Real.sqrt (∑ a : Fin (k+4) → Fin d, f a)
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _), ?_⟩
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun a _ ↦ hf a)]
    exact hsquares
  calc
    g.tensorNorm (curvaturePairContraction D i j σ) x ≤
        (d : ℝ) * g.tensorNorm (curvaturePairProduct D i j σ) x := hnorm
    _ = _ := by rw [tensorNorm_curvaturePairProduct]; ring

end PoincareConjecture.M04
