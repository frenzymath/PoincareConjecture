import PoincareConjecture.Proofs.M04.TensorMetricTrace
import Mathlib.Logic.Equiv.Fin.Basic








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def tensorPairing (g : RiemannianMetric n M) {r : ℕ}
    (S T : CovariantTensorEvaluation n M r) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
    S x (fun i => b (a i)) * T x (fun i => b (a i))

def pairedDiagonal {r : ℕ} {V : Type*} (a : Fin r → V) : Fin (r * 2) → V :=
  fun j => a ((finProdFinEquiv.symm j).1)

def tensorRankCast {k l : ℕ} (h : k = l)
    (T : CovariantTensorEvaluation n M k) : CovariantTensorEvaluation n M l :=
  fun x v => T x (fun i => v (Fin.cast h i))

noncomputable def tensorPairTrace (g : RiemannianMetric n M) {p r : ℕ}
    (A : CovariantTensorEvaluation n M (p + r * 2)) : CovariantTensorEvaluation n M p :=
  fun x v =>
    let b := g.orthonormalBasis x
    ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      A x (Fin.append v (pairedDiagonal (fun i => b (a i))))

omit [IsManifold (𝓡 n) ∞ M] in
private theorem tensorRankCast_trans {k l m : ℕ} (h : k = l) (h' : l = m)
    (T : CovariantTensorEvaluation n M k) :
    tensorRankCast h' (tensorRankCast h T) = tensorRankCast (h.trans h') T := by
  cases h
  cases h'
  rfl

private theorem isSmoothCovariantTensor_tensorRankCast {k l : ℕ} (h : k = l)
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (tensorRankCast h T) := by
  cases h
  exact hT

private theorem covariantTensorDerivative_tensorRankCast (D : LeviCivitaData g)
    {k l : ℕ} (h : k = l) (T : CovariantTensorEvaluation n M k) :
    D.covariantTensorDerivative (tensorRankCast h T) =
      tensorRankCast (congrArg (fun j => j + 1) h) (D.covariantTensorDerivative T) := by
  cases h
  rfl

private theorem tensorRankCast_tensorTraceLast (g : RiemannianMetric n M)
    {k l : ℕ} (h : k = l) (T : CovariantTensorEvaluation n M (k + 2)) :
    tensorRankCast h (tensorTraceLast g T) =
      tensorTraceLast g (tensorRankCast (congrArg (fun j => j + 2) h) T) := by
  cases h
  rfl

private theorem pairedDiagonal_snoc_cast {r : ℕ} {α : Type*}
    (a : Fin r → α) (z : α) (h : (r + 1) * 2 = r * 2 + 2) :
    (fun j => Fin.append (pairedDiagonal a) ![z, z] (Fin.cast h j)) =
      pairedDiagonal (Fin.snoc a z) := by
  funext j
  obtain ⟨⟨q, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  have hd : pairedDiagonal (Fin.snoc a z) (finProdFinEquiv (q, k)) =
      (Fin.snoc a z : Fin (r + 1) → α) q := by
    simp only [pairedDiagonal, Equiv.symm_apply_apply]
  rw [hd]
  cases q using Fin.lastCases with
  | last =>
    have hi : Fin.cast h (finProdFinEquiv (Fin.last r, k)) = Fin.natAdd (r * 2) k := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [hi, Fin.append_right, Fin.snoc_last]
    fin_cases k <;> rfl
  | cast q =>
    have hi : Fin.cast h (finProdFinEquiv (q.castSucc, k)) =
        Fin.castAdd 2 (finProdFinEquiv (q, k)) := by
      apply Fin.ext
      rfl
    rw [hi, Fin.append_left, Fin.snoc_castSucc]
    simp only [pairedDiagonal, Equiv.symm_apply_apply]

private theorem append_pairedDiagonal_snoc_cast {p r : ℕ} {α : Type*}
    (v : Fin p → α) (a : Fin r → α) (z : α)
    (h : p + (r + 1) * 2 = (p + r * 2) + 2) :
    (fun j => Fin.append (Fin.append v (pairedDiagonal a)) ![z, z] (Fin.cast h j)) =
      Fin.append v (pairedDiagonal (Fin.snoc a z)) := by
  have ha : Fin.append (Fin.append v (pairedDiagonal a)) ![z, z] =
      Fin.append v (Fin.append (pairedDiagonal a) ![z, z]) := by
    simpa only [Fin.cast_refl, Function.comp_id] using
      Fin.append_assoc v (pairedDiagonal a) ![z, z]
  rw [ha]
  let h0 : (r + 1) * 2 = r * 2 + 2 := by omega
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    have hi : Fin.cast h (Fin.castAdd ((r + 1) * 2) i) = Fin.castAdd (r * 2 + 2) i := by
      apply Fin.ext
      rfl
    rw [hi, Fin.append_left, Fin.append_left]
  · intro i
    have hi : Fin.cast h (Fin.natAdd p i) = Fin.natAdd p (Fin.cast h0 i) := by
      apply Fin.ext
      rfl
    rw [hi, Fin.append_right, Fin.append_right]
    exact congrFun (pairedDiagonal_snoc_cast a z h0) i

private theorem tensorPairTrace_zero (g : RiemannianMetric n M) {p : ℕ}
    (A : CovariantTensorEvaluation n M p) : tensorPairTrace (r := 0) g A = A := by
  classical
  funext x v
  have ha (a : Fin 0 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      Fin.append v (pairedDiagonal (fun i => g.orthonormalBasis x (a i))) = v := by
    simpa only [Fin.cast_refl, Function.comp_id] using
      Fin.append_right_nil v (pairedDiagonal (fun i => g.orthonormalBasis x (a i))) rfl
  simp only [tensorPairTrace, ha, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, pow_zero, one_smul]

private theorem tensorPairTrace_succ (g : RiemannianMetric n M) {p r : ℕ}
    (A : CovariantTensorEvaluation n M (p + (r + 1) * 2)) :
    tensorPairTrace g A =
      tensorPairTrace g
        (tensorTraceLast g
          (tensorRankCast (show p + (r + 1) * 2 = (p + r * 2) + 2 from by omega) A)) := by
  classical
  funext x v
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let b := g.orthonormalBasis x
  let h : p + (r + 1) * 2 = (p + r * 2) + 2 := by omega
  let f (a : Fin (r + 1) → Fin d) :=
    A x (Fin.append v (pairedDiagonal (fun i => b (a i))))
  have hsum : (∑ a, f a) = ∑ i : Fin d, ∑ a : Fin r → Fin d, f (Fin.snoc a i) := by
    calc
      _ = ∑ ia : Fin d × (Fin r → Fin d), f (Fin.snoc ia.2 ia.1) :=
        ((Fin.snocEquiv (fun _ : Fin (r + 1) => Fin d)).sum_comp f).symm
      _ = _ := by rw [Fintype.sum_prod_type]
  change (∑ a, f a) = ∑ a : Fin r → Fin d, ∑ i : Fin d,
    A x (fun j => Fin.append (Fin.append v (pairedDiagonal (fun k => b (a k))))
      ![b i, b i] (Fin.cast h j))
  rw [hsum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  have hb : (fun j => b ((Fin.snoc a i : Fin (r + 1) → Fin d) j)) =
      Fin.snoc (fun j => b (a j)) (b i) :=
    Fin.comp_snoc b a i
  change A x (Fin.append v
    (pairedDiagonal (fun j => b ((Fin.snoc a i : Fin (r + 1) → Fin d) j)))) = _
  rw [hb]
  exact congrArg (A x) (append_pairedDiagonal_snoc_cast v (fun j => b (a j)) (b i) h).symm

theorem isSmoothCovariantTensor_tensorPairTrace (g : RiemannianMetric n M) {p r : ℕ}
    {A : CovariantTensorEvaluation n M (p + r * 2)}
    (hA : IsSmoothCovariantTensor A) : IsSmoothCovariantTensor (tensorPairTrace g A) := by
  induction r generalizing p with
  | zero => simpa only [tensorPairTrace_zero] using hA
  | succ r ih =>
    rw [tensorPairTrace_succ]
    exact ih (isSmoothCovariantTensor_tensorTraceLast g
      (isSmoothCovariantTensor_tensorRankCast (by omega) hA))

private theorem append_cons_cast {p q : ℕ} {α : Type*}
    (u : α) (v : Fin p → α) (w : Fin q → α)
    (h : (p + q) + 1 = (p + 1) + q) :
    (fun j => Fin.append (Fin.cons u v) w (Fin.cast h j)) =
      Fin.cons u (Fin.append v w) := by
  funext j
  rw [Fin.append_cons]
  simp only [Function.comp_apply]
  apply congrArg (Fin.cons u (Fin.append v w))
  apply Fin.ext
  rfl

private theorem cons_rankCast {k l : ℕ} {α : Type*}
    (h : k = l) (u : α) (v : Fin l → α) :
    (fun j => (Fin.cons u v : Fin (l + 1) → α)
      (Fin.cast (congrArg (fun i => i + 1) h) j)) =
      (Fin.cons u (fun i => v (Fin.cast h i)) : Fin (k + 1) → α) := by
  cases h
  rfl

private theorem append_cons_cons_cast {p q : ℕ} {α : Type*}
    (u v : α) (w : Fin p → α) (z : Fin q → α)
    (h : (p + q) + 2 = (p + 2) + q) :
    (fun j => Fin.append (Fin.cons u (Fin.cons v w)) z (Fin.cast h j)) =
      Fin.cons u (Fin.cons v (Fin.append w z)) := by
  let h0 : (p + q) + 1 = (p + 1) + q := by omega
  let h1 : ((p + 1) + q) + 1 = (p + 2) + q := by omega
  have H0 := append_cons_cast v w z h0
  have H1 := append_cons_cast u (Fin.cons v w) z h1
  calc
    _ = (fun j : Fin ((p + q) + 2) =>
        (Fin.cons u (Fin.append (Fin.cons v w) z) : Fin (((p + 1) + q) + 1) → α)
        (Fin.cast (congrArg (fun i => i + 1) h0) j)) := by
      funext j
      exact congrFun H1 (Fin.cast (congrArg (fun i => i + 1) h0) j)
    _ = (Fin.cons u
        (fun i => Fin.append (Fin.cons v w) z (Fin.cast h0 i)) :
        Fin ((p + q) + 2) → α) :=
      cons_rankCast h0 u (Fin.append (Fin.cons v w) z)
    _ = _ := congrArg
      (fun t : Fin ((p + q) + 1) → α =>
        (Fin.cons u t : Fin ((p + q) + 2) → α)) H0

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
private theorem covariantTensorDerivative_tensorPairTrace_eq (D : LeviCivitaData g)
    {p r : ℕ} {A : CovariantTensorEvaluation n M (p + r * 2)}
    (hA : IsSmoothCovariantTensor A) :
    D.covariantTensorDerivative (tensorPairTrace g A) =
      tensorPairTrace g
        (tensorRankCast (show (p + r * 2) + 1 = (p + 1) + r * 2 from by omega)
          (D.covariantTensorDerivative A)) := by
  induction r generalizing p with
  | zero =>
    simp only [tensorPairTrace_zero]
    rfl
  | succ r ih =>
    let A0 : CovariantTensorEvaluation n M ((p + r * 2) + 2) :=
      tensorRankCast (show p + (r + 1) * 2 = (p + r * 2) + 2 from by omega) A
    have hA0 : IsSmoothCovariantTensor A0 :=
      isSmoothCovariantTensor_tensorRankCast (by omega) hA
    have hD0 : D.covariantTensorDerivative (tensorTraceLast g A0) =
        tensorTraceLast g (D.covariantTensorDerivative A0) := by
      funext x v
      exact covariantTensorDerivative_tensorTraceLast D hA0 x v
    rw [tensorPairTrace_succ]
    change D.covariantTensorDerivative (tensorPairTrace g (tensorTraceLast g A0)) = _
    rw [ih (isSmoothCovariantTensor_tensorTraceLast g hA0), hD0,
      tensorRankCast_tensorTraceLast, tensorPairTrace_succ]
    simp only [A0, covariantTensorDerivative_tensorRankCast, tensorRankCast_trans]

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivative_tensorPairTrace (D : LeviCivitaData g)
    {p r : ℕ} {A : CovariantTensorEvaluation n M (p + r * 2)}
    (hA : IsSmoothCovariantTensor A) (x : M) (u : TangentSpace (𝓡 n) x)
    (v : Fin p → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (tensorPairTrace g A) x (Fin.cons u v) =
      ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.covariantTensorDerivative A x
          (Fin.cons u (Fin.append v (pairedDiagonal (fun i => g.orthonormalBasis x (a i))))) := by
  classical
  rw [covariantTensorDerivative_tensorPairTrace_eq D hA]
  simp only [tensorPairTrace, tensorRankCast]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (D.covariantTensorDerivative A x)
  exact append_cons_cast u v (pairedDiagonal (fun i => g.orthonormalBasis x (a i))) (by omega)

set_option backward.isDefEq.respectTransparency false in
private theorem second_covariantTensorDerivative_tensorPairTrace_eq (D : LeviCivitaData g)
    {p r : ℕ} {A : CovariantTensorEvaluation n M (p + r * 2)}
    (hA : IsSmoothCovariantTensor A) :
    D.iteratedCovariantTensorDerivative (tensorPairTrace g A) 2 =
      tensorPairTrace g
        (tensorRankCast (show (p + r * 2) + 2 = (p + 2) + r * 2 from by omega)
          (D.iteratedCovariantTensorDerivative A 2)) := by
  let B : CovariantTensorEvaluation n M ((p + 1) + r * 2) :=
    tensorRankCast (show (p + r * 2) + 1 = (p + 1) + r * 2 from by omega)
      (D.covariantTensorDerivative A)
  have hB : IsSmoothCovariantTensor B := isSmoothCovariantTensor_tensorRankCast (by omega)
    (isSmoothCovariantTensor_covariantTensorDerivative D hA)
  have h1 : D.covariantTensorDerivative (tensorPairTrace g A) = tensorPairTrace g B :=
    covariantTensorDerivative_tensorPairTrace_eq D hA
  change D.covariantTensorDerivative (D.covariantTensorDerivative (tensorPairTrace g A)) = _
  rw [h1, covariantTensorDerivative_tensorPairTrace_eq D hB]
  simp only [B, covariantTensorDerivative_tensorRankCast, tensorRankCast_trans,
    LeviCivitaData.iteratedCovariantTensorDerivative]

set_option backward.isDefEq.respectTransparency false in
theorem second_covariantTensorDerivative_tensorPairTrace (D : LeviCivitaData g)
    {p r : ℕ} {A : CovariantTensorEvaluation n M (p + r * 2)}
    (hA : IsSmoothCovariantTensor A) (x : M) (u v : TangentSpace (𝓡 n) x)
    (w : Fin p → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (tensorPairTrace g A) 2 x
        (Fin.cons u (Fin.cons v w)) =
      ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.iteratedCovariantTensorDerivative A 2 x
          (Fin.cons u (Fin.cons v
            (Fin.append w (pairedDiagonal (fun i => g.orthonormalBasis x (a i)))))) := by
  classical
  rw [second_covariantTensorDerivative_tensorPairTrace_eq D hA]
  simp only [tensorPairTrace, tensorRankCast]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (D.iteratedCovariantTensorDerivative A 2 x)
  exact append_cons_cons_cast u v w
    (pairedDiagonal (fun i => g.orthonormalBasis x (a i))) (by omega)

end PoincareConjecture.M04

