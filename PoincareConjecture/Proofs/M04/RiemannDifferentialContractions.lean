import PoincareConjecture.Proofs.M04.ScalarContractions








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem smooth_tensor_add {k : ℕ} {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y v ↦ S y v + T y v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hS.1 x
    obtain ⟨B, hB⟩ := hT.1 x
    exact ⟨A + B, fun v ↦ congrArg₂ (· + ·) (hA v) (hB v)⟩
  · intro U hU X hX
    exact (hS.2 U hU X hX).add (hT.2 U hU X hX)

set_option backward.isDefEq.respectTransparency false in
private theorem derivative_tensor_add (D : LeviCivitaData g) {k : ℕ}
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w ↦ S y w + T y w) x v =
      D.covariantTensorDerivative S x v + D.covariantTensorDerivative T x v := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let X (i : Fin k) := FiberBundle.extend E (v i.succ)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hX (i : Fin k) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E))
      ∞ (T% (X i)) e.baseSet := contMDiffOn_extend_baseSet (v i.succ)
  have hSE : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ S y (fun i ↦ X i y)) x :=
    ((hS.2 e.baseSet e.open_baseSet X hX).contMDiffAt
      (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hTE : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ T y (fun i ↦ X i y)) x :=
    ((hT.2 e.baseSet e.open_baseSet X hX).contMDiffAt
      (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  simp only [LeviCivitaData.covariantTensorDerivative]
  rw [mvfderiv_fun_add hSE hTE]
  simp only [add_apply, Finset.sum_add_distrib]
  ring

private theorem derivative_tensor_neg (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k)
    (x : M) (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w ↦ -T y w) x v =
      -D.covariantTensorDerivative T x v := by
  simp only [LeviCivitaData.covariantTensorDerivative, mvfderiv_fun_neg,
    neg_apply, Finset.sum_neg_distrib]
  ring

private theorem second_derivative_tensor_neg (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k)
    (x : M) (v : Fin (k + 2) → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (fun y w ↦ -T y w) 2 x v =
      -D.iteratedCovariantTensorDerivative T 2 x v := by
  have he : D.covariantTensorDerivative (fun y w ↦ -T y w) =
      fun y w ↦ -D.covariantTensorDerivative T y w := by
    funext y w
    exact derivative_tensor_neg D T y w
  simp only [LeviCivitaData.iteratedCovariantTensorDerivative, he]
  exact derivative_tensor_neg D (D.covariantTensorDerivative T) x v

private theorem cons_five_tuple {α : Type*} (p a b c d e : α) :
    Fin.cons p ![a, b, c, d, e] = ![p, a, b, c, d, e] := by
  funext i
  fin_cases i <;> rfl

private theorem cons_cons_four_tuple {α : Type*} (p q a b c d : α) :
    Fin.cons p (Fin.cons q ![a, b, c, d]) = ![p, q, a, b, c, d] := by
  funext i
  fin_cases i <;> rfl

theorem riemann_secondCovariantDerivative_swap_first (D : LeviCivitaData g) (x : M)
    (p q a b c d : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, q, a, b, c, d] =
      -D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, q, b, a, c, d] := by
  classical
  let s := Equiv.swap (0 : Fin 4) 1
  have he : tensorPermute D.riemannEvaluation s = fun y w ↦ -D.riemannEvaluation y w := by
    funext y w
    change D.curvatureTensor y (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3)) = _
    have hs : s 0 = 1 ∧ s 1 = 0 ∧ s 2 = 2 ∧ s 3 = 3 := by decide
    rw [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
    exact curvatureTensor_swap_first D y (w 0) (w 1) (w 2) (w 3)
  have hv : ![a, b, c, d] ∘ s = ![b, a, c, d] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hp := secondCovariantTensorDerivative_tensorPermute D
    (isSmoothCovariantTensor_riemannEvaluation D) s x p q ![a, b, c, d]
  rw [he, second_derivative_tensor_neg, hv] at hp
  simpa only [cons_cons_four_tuple, neg_neg] using congrArg Neg.neg hp

theorem riemann_secondCovariantDerivative_swap_last (D : LeviCivitaData g) (x : M)
    (p q a b c d : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, q, a, b, c, d] =
      -D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, q, a, b, d, c] := by
  classical
  let s := Equiv.swap (2 : Fin 4) 3
  have he : tensorPermute D.riemannEvaluation s = fun y w ↦ -D.riemannEvaluation y w := by
    funext y w
    change D.curvatureTensor y (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3)) = _
    have hs : s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 3 ∧ s 3 = 2 := by decide
    rw [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
    exact curvatureTensor_swap_last D y (w 0) (w 1) (w 3) (w 2)
  have hv : ![a, b, c, d] ∘ s = ![a, b, d, c] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hp := secondCovariantTensorDerivative_tensorPermute D
    (isSmoothCovariantTensor_riemannEvaluation D) s x p q ![a, b, c, d]
  rw [he, second_derivative_tensor_neg, hv] at hp
  simpa only [cons_cons_four_tuple, neg_neg] using congrArg Neg.neg hp

theorem riemann_secondCovariantDerivative_pair_exchange (D : LeviCivitaData g) (x : M)
    (p q a b c d : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, q, a, b, c, d] =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, q, c, d, a, b] := by
  classical
  let s := (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)
  have he : tensorPermute D.riemannEvaluation s = D.riemannEvaluation := by
    funext y w
    change D.curvatureTensor y (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3)) = _
    have hs : s 0 = 2 ∧ s 1 = 3 ∧ s 2 = 0 ∧ s 3 = 1 := by decide
    rw [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
    exact curvatureTensor_pair_exchange D y (w 2) (w 3) (w 0) (w 1)
  have hv : ![a, b, c, d] ∘ s = ![c, d, a, b] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hp := secondCovariantTensorDerivative_tensorPermute D
    (isSmoothCovariantTensor_riemannEvaluation D) s x p q ![a, b, c, d]
  rw [he, hv] at hp
  exact hp

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem riemann_secondCovariantDerivative_bianchi (D : LeviCivitaData g) (x : M)
    (p q a b c d : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, q, a, b, c, d] +
      D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, a, b, q, c, d] +
      D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x ![p, b, q, a, c, d] = 0 := by
  classical
  let K := D.covariantTensorDerivative D.riemannEvaluation
  have hK : IsSmoothCovariantTensor K :=
    isSmoothCovariantTensor_covariantTensorDerivative D
      (isSmoothCovariantTensor_riemannEvaluation D)
  let s := (Equiv.swap (1 : Fin 5) 2).trans (Equiv.swap (0 : Fin 5) 1)
  let r := s.trans s
  have hs (y : M) (a b c d e : TangentSpace (𝓡 n) y) :
      ![a, b, c, d, e] ∘ s = ![b, c, a, d, e] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hr (y : M) (a b c d e : TangentSpace (𝓡 n) y) :
      ![a, b, c, d, e] ∘ r = ![c, a, b, d, e] := by
    funext i
    fin_cases i <;> simp [r, s, Equiv.swap_apply_def]
  have hS := isSmoothCovariantTensor_tensorPermute hK s
  have hR := isSmoothCovariantTensor_tensorPermute hK r
  have he : (fun y w ↦ K y w + tensorPermute K s y w + tensorPermute K r y w) =
      (fun (y : M) (_ : Fin 5 → TangentSpace (𝓡 n) y) ↦ (0 : ℝ)) := by
    funext y w
    have hw : w = ![w 0, w 1, w 2, w 3, w 4] := by
      funext i
      fin_cases i <;> rfl
    change K y w + K y (w ∘ s) + K y (w ∘ r) = 0
    rw [hw, hs y, hr y]
    exact riemann_second_bianchi D y (w 0) (w 1) (w 2) (w 3) (w 4)
  have hd := congrArg (fun T : CovariantTensorEvaluation n M 5 ↦
    D.covariantTensorDerivative T x ![p, q, a, b, c, d]) he
  rw [derivative_tensor_add D (smooth_tensor_add hK hS) hR,
    derivative_tensor_add D hK hS] at hd
  have hs' := covariantTensorDerivative_tensorPermute D hK s x p ![q, a, b, c, d]
  have hr' := covariantTensorDerivative_tensorPermute D hK r x p ![q, a, b, c, d]
  rw [hs x] at hs'
  rw [hr x] at hr'
  simp only [cons_five_tuple] at hs' hr'
  rw [hs', hr'] at hd
  have hz : D.covariantTensorDerivative
      (fun (y : M) (_ : Fin 5 → TangentSpace (𝓡 n) y) ↦ (0 : ℝ))
      x ![p, q, a, b, c, d] = 0 := by
    simp [LeviCivitaData.covariantTensorDerivative, mvfderiv_const]
  rw [hz] at hd
  simpa only [K, LeviCivitaData.iteratedCovariantTensorDerivative] using hd

private theorem append_two_tuple {α : Type*} (v : Fin 2 → α) (a b : α) :
    Fin.append v ![a, b] = ![v 0, v 1, a, b] := by
  funext i
  fin_cases i <;> rfl

private theorem append_four_tuple {α : Type*} (v : Fin 4 → α) (a b : α) :
    Fin.append v ![a, b] = ![v 0, v 1, v 2, v 3, a, b] := by
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem ricci_secondCovariantDerivative_curvature_trace (D : LeviCivitaData g) (x : M)
    (p q a c : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![p, q, a, c] =
      ∑ i, D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
        ![p, q, a, g.orthonormalBasis x i, c, g.orthonormalBasis x i] := by
  classical
  let s := Equiv.swap (1 : Fin 4) 2
  let R := tensorPermute D.riemannEvaluation s
  have hR : IsSmoothCovariantTensor R :=
    isSmoothCovariantTensor_tensorPermute (isSmoothCovariantTensor_riemannEvaluation D) s
  have he : tensorTraceLast g R = D.ricciEvaluation := by
    funext y w
    simp [R, tensorTraceLast, tensorPermute, append_two_tuple, s, Equiv.swap_apply_def,
      LeviCivitaData.riemannEvaluation, LeviCivitaData.ricciEvaluation, LeviCivitaData.ricci]
  have hfirst : D.covariantTensorDerivative (tensorTraceLast g R) =
      tensorTraceLast g (D.covariantTensorDerivative R) := by
    funext y w
    exact covariantTensorDerivative_tensorTraceLast D hR y w
  have ht := covariantTensorDerivative_tensorTraceLast D
    (isSmoothCovariantTensor_covariantTensorDerivative D hR) x ![p, q, a, c]
  rw [← hfirst, he] at ht
  have hv (v w : TangentSpace (𝓡 n) x) : ![a, c, v, w] ∘ s = ![a, v, c, w] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  calc
    _ = tensorTraceLast g (D.covariantTensorDerivative (D.covariantTensorDerivative R))
        x ![p, q, a, c] := ht
    _ = _ := by
      unfold tensorTraceLast
      apply Finset.sum_congr rfl
      intro i hi
      have hp := secondCovariantTensorDerivative_tensorPermute D
        (isSmoothCovariantTensor_riemannEvaluation D) s x p q
        ![a, c, g.orthonormalBasis x i, g.orthonormalBasis x i]
      rw [hv] at hp
      simpa only [R, append_four_tuple, cons_cons_four_tuple,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        LeviCivitaData.iteratedCovariantTensorDerivative] using hp

set_option maxHeartbeats 1200000 in

theorem riemann_secondCovariantDerivative_divergence (D : LeviCivitaData g) (x : M)
    (p b c d : TangentSpace (𝓡 n) x) :
    (∑ i, D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
      ![p, g.orthonormalBasis x i, g.orthonormalBasis x i, b, c, d]) =
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![p, c, d, b] -
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![p, d, c, b] := by
  classical
  let e := g.orthonormalBasis x
  let T := D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
  let H := D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
  have htrace (a b c d : TangentSpace (𝓡 n) x) :
      H ![a, b, c, d] = ∑ i, T ![a, b, c, e i, d, e i] :=
    ricci_secondCovariantDerivative_curvature_trace D x a b c d
  have h0 : (∑ i, (T ![p, e i, c, d, e i, b] +
      T ![p, c, d, e i, e i, b] + T ![p, d, e i, c, e i, b])) = 0 := by
    have hi (i) : T ![p, e i, c, d, e i, b] +
        T ![p, c, d, e i, e i, b] + T ![p, d, e i, c, e i, b] = 0 :=
      riemann_secondCovariantDerivative_bianchi D x p (e i) c d (e i) b
    simp only [hi, Finset.sum_const_zero]
  have h1 : (∑ i, T ![p, e i, c, d, e i, b]) =
      ∑ i, T ![p, e i, e i, b, c, d] := by
    apply Finset.sum_congr rfl
    intro i hi
    exact riemann_secondCovariantDerivative_pair_exchange D x p (e i) c d (e i) b
  have h2 : (∑ i, T ![p, c, d, e i, e i, b]) = -H ![p, c, d, b] := by
    rw [htrace, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact riemann_secondCovariantDerivative_swap_last D x p c d (e i) (e i) b
  have h3 : (∑ i, T ![p, d, e i, c, e i, b]) = H ![p, d, c, b] := by
    rw [htrace]
    apply Finset.sum_congr rfl
    intro i hi
    have hs : T ![p, d, e i, c, e i, b] = -T ![p, d, c, e i, e i, b] :=
      riemann_secondCovariantDerivative_swap_first D x p d (e i) c (e i) b
    have hl : T ![p, d, c, e i, e i, b] = -T ![p, d, c, e i, b, e i] :=
      riemann_secondCovariantDerivative_swap_last D x p d c (e i) (e i) b
    rw [hs, hl, neg_neg]
  simp only [Finset.sum_add_distrib, h1, h2, h3] at h0
  change (∑ i, T ![p, e i, e i, b, c, d]) = H ![p, c, d, b] - H ![p, d, c, b]
  linarith only [h0]

end PoincareConjecture.M04

