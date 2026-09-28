import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.ScalarTrace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorMetricTrace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.SecondBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem append_one_tuple {α : Type*} (v : Fin 1 → α) (a b : α) :
    Fin.append v ![a, b] = ![v 0, a, b] := by
  funext i
  fin_cases i <;> rfl

private theorem append_two_tuple {α : Type*} (v : Fin 2 → α) (a b : α) :
    Fin.append v ![a, b] = ![v 0, v 1, a, b] := by
  funext i
  fin_cases i <;> rfl

private theorem append_three_tuple {α : Type*} (v : Fin 3 → α) (a b : α) :
    Fin.append v ![a, b] = ![v 0, v 1, v 2, a, b] := by
  funext i
  fin_cases i <;> rfl

def tensorPermute {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (s : Equiv.Perm (Fin k)) : CovariantTensorEvaluation n M k :=
  fun x v ↦ T x (v ∘ s)

theorem isSmoothCovariantTensor_tensorPermute {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (s : Equiv.Perm (Fin k)) : IsSmoothCovariantTensor (tensorPermute T s) := by
  constructor
  · intro x
    obtain ⟨L, hL⟩ := hT.1 x
    exact ⟨L.domDomCongr s, fun v ↦ hL (v ∘ s)⟩
  · intro U hU V hV
    exact hT.2 U hU (fun i ↦ V (s i)) (fun i ↦ hV (s i))

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivative_tensorPermute {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (_hT : IsSmoothCovariantTensor T) (s : Equiv.Perm (Fin k))
    (x : M) (a : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (tensorPermute T s) x (Fin.cons a v) =
      D.covariantTensorDerivative T x (Fin.cons a (v ∘ s)) := by
  classical
  simp only [LeviCivitaData.covariantTensorDerivative, tensorPermute,
    Fin.cons_zero, Fin.cons_succ]
  congr 1
  refine Fintype.sum_equiv s.symm _ _ ?_
  intro i
  simp only [Function.comp_def, s.apply_symm_apply]
  apply congrArg (T x)
  change (Function.update v i (D.connection (FiberBundle.extend _ (v i)) x a)) ∘ s = _
  exact Function.update_comp_equiv _ _ _ _

private def liftTensorPermutation {k : ℕ} (s : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (k + 1)) :=
  (finSuccEquiv k).trans ((Equiv.optionCongr s).trans (finSuccEquiv k).symm)

private theorem cons_comp_lift {α : Type*} {k : ℕ} (s : Equiv.Perm (Fin k))
    (a : α) (v : Fin k → α) :
    Fin.cons a v ∘ liftTensorPermutation s = Fin.cons a (v ∘ s) := by
  funext i
  cases i using Fin.cases <;> simp [liftTensorPermutation, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
theorem secondCovariantTensorDerivative_tensorPermute {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (s : Equiv.Perm (Fin k))
    (x : M) (a b : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (tensorPermute T s) 2 x
        (Fin.cons a (Fin.cons b v)) =
      D.iteratedCovariantTensorDerivative T 2 x (Fin.cons a (Fin.cons b (v ∘ s))) := by
  have he : D.covariantTensorDerivative (tensorPermute T s) =
      tensorPermute (D.covariantTensorDerivative T) (liftTensorPermutation s) := by
    funext y w
    conv_lhs => rw [← Fin.cons_self_tail w]
    rw [covariantTensorDerivative_tensorPermute D hT]
    change _ = D.covariantTensorDerivative T y (w ∘ liftTensorPermutation s)
    conv_rhs => rw [← Fin.cons_self_tail w]
    rw [cons_comp_lift]
  simp only [LeviCivitaData.iteratedCovariantTensorDerivative, he]
  rw [covariantTensorDerivative_tensorPermute D
    (isSmoothCovariantTensor_covariantTensorDerivative D hT), cons_comp_lift]

private def scalarTensor (f : M → ℝ) : CovariantTensorEvaluation n M 0 :=
  fun x _ ↦ f x

private theorem derivative_scalarTensor {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (v : Fin 1 → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (scalarTensor f) x v = mvfderiv (𝓡 n) f x (v 0) := by
  simp [LeviCivitaData.covariantTensorDerivative, scalarTensor]

private theorem second_derivative_scalarTensor {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (v : Fin 2 → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.covariantTensorDerivative (scalarTensor f)) x v =
      D.hessian f x (v 0) (v 1) := by
  rw [LeviCivitaData.covariantTensorDerivative]
  simp only [derivative_scalarTensor, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Function.update_self, LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self, add_zero]
  rfl

private theorem tensorTraceLast_ricci {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    tensorTraceLast g D.ricciEvaluation = scalarTensor D.scalarCurvature := by
  funext x v
  have hv : v = Fin.elim0 := funext fun i ↦ Fin.elim0 i
  rw [hv]
  simp [tensorTraceLast, scalarTensor, LeviCivitaData.ricciEvaluation,
    LeviCivitaData.scalarCurvature]

theorem ricci_covariantDerivative_symm {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.ricciEvaluation x ![a, b, c] =
      D.covariantTensorDerivative D.ricciEvaluation x ![a, c, b] := by
  classical
  let s := Equiv.swap (0 : Fin 2) 1
  have he : tensorPermute D.ricciEvaluation s = D.ricciEvaluation := by
    funext y w
    change D.ricci y (w (s 0)) (w (s 1)) = D.ricci y (w 0) (w 1)
    simp only [s, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact ricci_symm D y _ _
  have hv : ![b, c] ∘ s = ![c, b] := by
    funext i
    fin_cases i <;> simp [s]
  have hp := covariantTensorDerivative_tensorPermute D
    (isSmoothCovariantTensor_ricciEvaluation D) s x a ![b, c]
  rw [he, hv] at hp
  exact hp

theorem ricci_secondCovariantDerivative_symm {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, b, c, d] =
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, b, d, c] := by
  classical
  let s := Equiv.swap (0 : Fin 2) 1
  have he : tensorPermute D.ricciEvaluation s = D.ricciEvaluation := by
    funext y w
    change D.ricci y (w (s 0)) (w (s 1)) = D.ricci y (w 0) (w 1)
    simp only [s, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact ricci_symm D y _ _
  have hv : ![c, d] ∘ s = ![d, c] := by
    funext i
    fin_cases i <;> simp [s]
  have hp := secondCovariantTensorDerivative_tensorPermute D
    (isSmoothCovariantTensor_ricciEvaluation D) s x a b ![c, d]
  rw [he, hv] at hp
  exact hp

theorem ricci_covariantDerivative_metric_trace {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative D.ricciEvaluation x
      ![a, g.orthonormalBasis x i, g.orthonormalBasis x i]) =
        mvfderiv (𝓡 n) D.scalarCurvature x a := by
  have ht := covariantTensorDerivative_tensorTraceLast D
    (isSmoothCovariantTensor_ricciEvaluation D) x ![a]
  rw [tensorTraceLast_ricci, derivative_scalarTensor] at ht
  simpa only [tensorTraceLast, append_one_tuple, Matrix.cons_val_zero] using ht.symm

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem ricci_secondCovariantDerivative_metric_trace {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a b : TangentSpace (𝓡 n) x) :
    (∑ i, D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
      ![a, b, g.orthonormalBasis x i, g.orthonormalBasis x i]) =
        D.hessian D.scalarCurvature x a b := by
  have he : D.covariantTensorDerivative (tensorTraceLast g D.ricciEvaluation) =
      tensorTraceLast g (D.covariantTensorDerivative D.ricciEvaluation) := by
    funext y w
    exact covariantTensorDerivative_tensorTraceLast D
      (isSmoothCovariantTensor_ricciEvaluation D) y w
  have ht := covariantTensorDerivative_tensorTraceLast D
    (isSmoothCovariantTensor_covariantTensorDerivative D
      (isSmoothCovariantTensor_ricciEvaluation D)) x ![a, b]
  rw [← he, tensorTraceLast_ricci, second_derivative_scalarTensor] at ht
  simpa only [tensorTraceLast, append_two_tuple, Matrix.cons_val_zero, Matrix.cons_val_one,
    LeviCivitaData.iteratedCovariantTensorDerivative] using ht.symm

set_option backward.isDefEq.respectTransparency false in
private theorem derivative_tensor_neg {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (x : M) (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w ↦ -T y w) x v =
      -D.covariantTensorDerivative T x v := by
  simp only [LeviCivitaData.covariantTensorDerivative, mvfderiv_fun_neg,
    neg_apply, Finset.sum_neg_distrib]
  ring

private theorem riemann_derivative_swap_first {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
      -D.covariantTensorDerivative D.riemannEvaluation x ![a, c, b, d, e] := by
  classical
  let s := Equiv.swap (0 : Fin 4) 1
  have he : tensorPermute D.riemannEvaluation s = fun y w ↦ -D.riemannEvaluation y w := by
    funext y w
    change D.curvatureTensor y (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3)) = _
    have hs : s 0 = 1 ∧ s 1 = 0 ∧ s 2 = 2 ∧ s 3 = 3 := by decide
    rw [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
    exact curvatureTensor_swap_first D y (w 0) (w 1) (w 2) (w 3)
  have hv : ![b, c, d, e] ∘ s = ![c, b, d, e] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hp := covariantTensorDerivative_tensorPermute D
    (isSmoothCovariantTensor_riemannEvaluation D) s x a ![b, c, d, e]
  rw [he, derivative_tensor_neg, hv] at hp
  change -D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
    D.covariantTensorDerivative D.riemannEvaluation x ![a, c, b, d, e] at hp
  linarith only [hp]

private theorem riemann_derivative_swap_last {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
      -D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, e, d] := by
  classical
  let s := Equiv.swap (2 : Fin 4) 3
  have he : tensorPermute D.riemannEvaluation s = fun y w ↦ -D.riemannEvaluation y w := by
    funext y w
    change D.curvatureTensor y (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3)) = _
    have hs : s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 3 ∧ s 3 = 2 := by decide
    rw [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
    exact curvatureTensor_swap_last D y (w 0) (w 1) (w 3) (w 2)
  have hv : ![b, c, d, e] ∘ s = ![b, c, e, d] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hp := covariantTensorDerivative_tensorPermute D
    (isSmoothCovariantTensor_riemannEvaluation D) s x a ![b, c, d, e]
  rw [he, derivative_tensor_neg, hv] at hp
  change -D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
    D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, e, d] at hp
  linarith only [hp]

theorem ricci_covariantDerivative_curvature_trace {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.ricciEvaluation x ![a, b, c] =
      ∑ i, D.covariantTensorDerivative D.riemannEvaluation x
        ![a, b, g.orthonormalBasis x i, c, g.orthonormalBasis x i] := by
  classical
  let s := Equiv.swap (1 : Fin 4) 2
  have he : tensorTraceLast g (tensorPermute D.riemannEvaluation s) = D.ricciEvaluation := by
    funext y w
    simp [tensorTraceLast, tensorPermute, append_two_tuple, s, Equiv.swap_apply_def,
      LeviCivitaData.riemannEvaluation, LeviCivitaData.ricciEvaluation,
      LeviCivitaData.ricci]
  have hv (d e : TangentSpace (𝓡 n) x) : ![b, c, d, e] ∘ s = ![b, d, c, e] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hterm (i) :
      D.covariantTensorDerivative (tensorPermute D.riemannEvaluation s) x
        ![a, b, c, g.orthonormalBasis x i, g.orthonormalBasis x i] =
      D.covariantTensorDerivative D.riemannEvaluation x
        ![a, b, g.orthonormalBasis x i, c, g.orthonormalBasis x i] := by
    have hp := covariantTensorDerivative_tensorPermute D
      (isSmoothCovariantTensor_riemannEvaluation D) s x a
      ![b, c, g.orthonormalBasis x i, g.orthonormalBasis x i]
    rw [hv] at hp
    exact hp
  have ht := covariantTensorDerivative_tensorTraceLast D
    (isSmoothCovariantTensor_tensorPermute (isSmoothCovariantTensor_riemannEvaluation D) s)
    x ![a, b, c]
  rw [he] at ht
  simpa only [tensorTraceLast, append_three_tuple, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hterm] using ht

set_option maxHeartbeats 1200000 in

theorem ricci_covariantDerivative_contracted {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative D.ricciEvaluation x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i, a]) =
        (1 / 2 : ℝ) * mvfderiv (𝓡 n) D.scalarCurvature x a := by
  classical
  let e := g.orthonormalBasis x
  let Q := D.covariantTensorDerivative D.riemannEvaluation x
  let K := D.covariantTensorDerivative D.ricciEvaluation x
  have h0 : (∑ i, ∑ j, (Q ![a, e i, e j, e i, e j] +
      Q ![e i, e j, a, e i, e j] + Q ![e j, a, e i, e i, e j])) = 0 := by
    have he (i j) : Q ![a, e i, e j, e i, e j] +
        Q ![e i, e j, a, e i, e j] + Q ![e j, a, e i, e i, e j] = 0 :=
      riemann_second_bianchi D x a (e i) (e j) (e i) (e j)
    simp only [he, Finset.sum_const_zero]
  have h1 : (∑ i, ∑ j, Q ![a, e i, e j, e i, e j]) =
      mvfderiv (𝓡 n) D.scalarCurvature x a := by
    calc
      _ = ∑ i, K ![a, e i, e i] := by
        apply Finset.sum_congr rfl
        intro i _
        exact (ricci_covariantDerivative_curvature_trace D x a (e i) (e i)).symm
      _ = _ := ricci_covariantDerivative_metric_trace D x a
  have h2 : (∑ i, ∑ j, Q ![e i, e j, a, e i, e j]) =
      -(∑ i, K ![e i, e i, a]) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = -(∑ j, Q ![e i, a, e j, e i, e j]) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        exact riemann_derivative_swap_first D x (e i) (e j) a (e i) (e j)
      _ = -K ![e i, a, e i] := by
        rw [← ricci_covariantDerivative_curvature_trace D x (e i) a (e i)]
      _ = _ := congrArg Neg.neg (ricci_covariantDerivative_symm D x (e i) a (e i))
  have h3 : (∑ i, ∑ j, Q ![e j, a, e i, e i, e j]) =
      -(∑ i, K ![e i, e i, a]) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = -(∑ i, Q ![e j, a, e i, e j, e i]) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact riemann_derivative_swap_last D x (e j) a (e i) (e i) (e j)
      _ = -K ![e j, a, e j] := by
        rw [← ricci_covariantDerivative_curvature_trace D x (e j) a (e j)]
      _ = _ := congrArg Neg.neg (ricci_covariantDerivative_symm D x (e j) a (e j))
  simp only [Finset.sum_add_distrib, h1, h2, h3] at h0
  change (∑ i, K ![e i, e i, a]) = _
  linarith only [h0]

set_option maxHeartbeats 1500000 in

set_option backward.isDefEq.respectTransparency false in
theorem ricci_secondCovariantDerivative_contracted {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (a b : TangentSpace (𝓡 n) x) :
    (∑ i, D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
      ![a, g.orthonormalBasis x i, g.orthonormalBasis x i, b]) =
        (1 / 2 : ℝ) * D.hessian D.scalarCurvature x a b := by
  classical
  let K := D.covariantTensorDerivative D.ricciEvaluation
  have hK : IsSmoothCovariantTensor K :=
    isSmoothCovariantTensor_covariantTensorDerivative D (isSmoothCovariantTensor_ricciEvaluation D)
  let s := (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1)
  let P := tensorPermute K s
  let S0 := scalarTensor (n := n) D.scalarCurvature
  let S1 := D.covariantTensorDerivative S0
  have hS0 : IsSmoothCovariantTensor S0 := by
    dsimp only [S0]
    rw [← tensorTraceLast_ricci D]
    exact isSmoothCovariantTensor_tensorTraceLast g (isSmoothCovariantTensor_ricciEvaluation D)
  have hS1 : IsSmoothCovariantTensor S1 := isSmoothCovariantTensor_covariantTensorDerivative D hS0
  have he : tensorTraceLast g P = fun y v ↦ (1 / 2 : ℝ) * S1 y v := by
    funext y v
    have hv (c : TangentSpace (𝓡 n) y) :
        Fin.append v ![c, c] ∘ s = ![c, c, v 0] := by
      funext i
      fin_cases i <;> simp [s, Equiv.swap_apply_def,
        append_one_tuple]
    change (∑ i, K y (Fin.append v ![g.orthonormalBasis y i, g.orthonormalBasis y i] ∘ s)) =
      (1 / 2 : ℝ) * D.covariantTensorDerivative (scalarTensor D.scalarCurvature) y v
    simp only [hv, derivative_scalarTensor]
    exact ricci_covariantDerivative_contracted D y (v 0)
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let B := FiberBundle.extend E b
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% B) e.baseSet :=
    contMDiffOn_extend_baseSet b
  have hW (i : Fin 1) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E))
      ∞ (T% (![B] i)) e.baseSet := by
    fin_cases i
    exact hB
  have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ S1 y ![B y]) x := by
    have hs := hS1.2 e.baseSet e.open_baseSet ![B] hW
    have hp (y : M) : (fun i ↦ ![B] i y) = ![B y] := by
      funext i
      fin_cases i
      rfl
    simp only [hp] at hs
    exact (hs.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hRaw (T : CovariantTensorEvaluation n M 1) :
      D.covariantTensorDerivative T x ![a, b] =
        mvfderiv (𝓡 n) (fun y ↦ T y ![B y]) x a -
          T x ![D.connection B x a] := by
    have htail (y : M) :
        (fun i : Fin 1 ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (![a, b] i.succ) y) = ![B y] := by
      funext i
      fin_cases i
      rfl
    have hfun : (fun y ↦ T y (fun i : Fin 1 ↦
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (![a, b] i.succ) y)) =
        (fun y ↦ T y ![B y]) := by
      funext y
      exact congrArg (T y) (htail y)
    have hu (z : TangentSpace (𝓡 n) x) :
        Function.update (fun j : Fin 1 ↦ ![a, b] j.succ) 0 z = ![z] := by
      funext i
      fin_cases i
      simp
    simp only [LeviCivitaData.covariantTensorDerivative, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Matrix.cons_val_zero, hu, add_zero]
    rw [hfun]
    rfl
  have hscale : D.covariantTensorDerivative (fun y v ↦ (1 / 2 : ℝ) * S1 y v) x ![a, b] =
      (1 / 2 : ℝ) * D.covariantTensorDerivative S1 x ![a, b] := by
    rw [hRaw, hRaw]
    have hd : mvfderiv (𝓡 n) (fun y ↦ (1 / 2 : ℝ) * S1 y ![B y]) x a =
        (1 / 2 : ℝ) * mvfderiv (𝓡 n) (fun y ↦ S1 y ![B y]) x a := by
      erw [mvfderiv_fun_mul (mdifferentiableAt_const (c := (1 / 2 : ℝ))) hf]
      simp only [mvfderiv_const, add_apply, smul_apply, smul_eq_mul, zero_apply,
        mul_zero, add_zero]
    rw [hd]
    ring
  have hL : D.covariantTensorDerivative (tensorTraceLast g P) x ![a, b] =
      (1 / 2 : ℝ) * D.hessian D.scalarCurvature x a b := by
    rw [he, hscale]
    change (1 / 2 : ℝ) * D.covariantTensorDerivative
      (D.covariantTensorDerivative (scalarTensor D.scalarCurvature)) x ![a, b] = _
    rw [second_derivative_scalarTensor]
    rfl
  have hv (c d : TangentSpace (𝓡 n) x) : ![b, c, d] ∘ s = ![c, d, b] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hterm (c : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative (tensorPermute K s) x ![a, b, c, c] =
        D.covariantTensorDerivative K x ![a, c, c, b] := by
    have hp := covariantTensorDerivative_tensorPermute D hK s x a ![b, c, c]
    rw [hv] at hp
    exact hp
  have ht := covariantTensorDerivative_tensorTraceLast D
    (isSmoothCovariantTensor_tensorPermute hK s) x ![a, b]
  rw [hL] at ht
  simp only [tensorTraceLast, append_two_tuple, Matrix.cons_val_zero,
    Matrix.cons_val_one] at ht
  simpa only [hterm, K, LeviCivitaData.iteratedCovariantTensorDerivative] using ht.symm

end PoincareConjecture.RicciFlowAnalysis
