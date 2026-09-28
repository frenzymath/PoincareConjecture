import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Energy.Product
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Energy.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private def scalarTensor (q : M → ℝ) :
    CovariantTensorEvaluation n M 0 := fun x _ => q x

private theorem tensorPairing_self (g : RiemannianMetric n M) {r : ℕ}
    (T : CovariantTensorEvaluation n M r) (x : M) :
    tensorPairing g T T x = (g.tensorNorm T x) ^ 2 := by
  classical
  unfold tensorPairing RiemannianMetric.tensorNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [pow_two]

private theorem pairedDiagonal_component {r : ℕ} {V : Type*}
    (a : Fin r → V) (k : Fin 2) :
    (fun i => pairedDiagonal a (finProdFinEquiv (i, k))) = a := by
  funext i
  simp only [pairedDiagonal, Equiv.symm_apply_apply]

private theorem append_zero_cast {k : ℕ} {V : Type*}
    (v : Fin 0 → V) (w : Fin k → V) (h : k = 0 + k) :
    (fun i => Fin.append v w (Fin.cast h i)) = w := by
  funext i
  have hi : Fin.cast h i = Fin.natAdd 0 i := by
    apply Fin.ext
    simp
  rw [hi, Fin.append_right]

private theorem isSmoothCovariantTensor_rankCast {k l : ℕ} (h : k = l)
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (tensorRankCast h T) := by
  cases h
  exact hT

private theorem second_derivative_rankCast (D : LeviCivitaData g)
    {k l : ℕ} (h : k = l) (T : CovariantTensorEvaluation n M k)
    (x : M) (u v : TangentSpace (𝓡 n) x)
    (w : Fin l → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (tensorRankCast h T) 2 x
        (Fin.cons u (Fin.cons v w)) =
      D.iteratedCovariantTensorDerivative T 2 x
        (Fin.cons u (Fin.cons v (fun i => w (Fin.cast h i)))) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tensorPairTrace_pairedProduct (g : RiemannianMetric n M)
    {r : ℕ} (S T : CovariantTensorEvaluation n M r) :
    tensorPairTrace (p := 0) (r := r) g
        (tensorRankCast (Nat.zero_add (r * 2)).symm (pairedProduct S T)) =
      scalarTensor (tensorPairing g S T) := by
  classical
  funext x v
  change (∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      pairedProduct S T x
        (fun j => Fin.append v
          (pairedDiagonal (fun i => g.orthonormalBasis x (a i)))
          (Fin.cast (Nat.zero_add (r * 2)).symm j))) =
    ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      S x (fun i => g.orthonormalBasis x (a i)) *
        T x (fun i => g.orthonormalBasis x (a i))
  apply Finset.sum_congr rfl
  intro a _
  rw [append_zero_cast]
  simp only [pairedProduct, pairedDiagonal_component]

private theorem derivative_scalarTensor (D : LeviCivitaData g)
    (q : M → ℝ) (x : M) (v : Fin 1 → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (scalarTensor q) x v =
      mvfderiv (𝓡 n) q x (v 0) := by
  simp [LeviCivitaData.covariantTensorDerivative, scalarTensor]

private theorem second_derivative_scalarTensor (D : LeviCivitaData g)
    (q : M → ℝ) (x : M) (v : Fin 2 → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (scalarTensor q) 2 x v =
      D.hessian q x (v 0) (v 1) := by
  change D.covariantTensorDerivative
    (D.covariantTensorDerivative (scalarTensor q)) x v = _
  have h01 : (Fin.succ 0 : Fin 2) = 1 := by decide
  rw [LeviCivitaData.covariantTensorDerivative]
  simp only [derivative_scalarTensor, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Function.update_self, LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self, add_zero, h01]

private theorem contMDiff_scalar_of_smoothTensor {q : M → ℝ}
    (hq : IsSmoothCovariantTensor (scalarTensor (n := n) q)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q := by
  let X : Fin 0 → (x : M) → TangentSpace (𝓡 n) x := fun i => Fin.elim0 i
  have hX (i : Fin 0) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X i)) univ :=
    Fin.elim0 i
  have h := hq.2 univ isOpen_univ X hX
  change ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q univ at h
  exact contMDiffOn_univ.mp h

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_tensorNorm_sq (g : RiemannianMetric n M) {r : ℕ}
    {T : CovariantTensorEvaluation n M r} (hT : IsSmoothCovariantTensor T) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (g.tensorNorm T y) ^ 2) := by
  let A : CovariantTensorEvaluation n M (0 + r * 2) :=
    tensorRankCast (Nat.zero_add (r * 2)).symm (pairedProduct T T)
  have hA : IsSmoothCovariantTensor A :=
    isSmoothCovariantTensor_rankCast _ (isSmoothCovariantTensor_pairedProduct hT hT)
  have hScalar : tensorPairTrace (p := 0) (r := r) g A =
      scalarTensor (fun y => (g.tensorNorm T y) ^ 2) := by
    change tensorPairTrace (p := 0) (r := r) g
      (tensorRankCast (Nat.zero_add (r * 2)).symm (pairedProduct T T)) = _
    rw [tensorPairTrace_pairedProduct]
    exact congrArg (scalarTensor (n := n))
      (funext fun y => tensorPairing_self g T y)
  have h := isSmoothCovariantTensor_tensorPairTrace (p := 0) (r := r) g hA
  rw [hScalar] at h
  exact contMDiff_scalar_of_smoothTensor h

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem hessian_tensorNorm_sq (D : LeviCivitaData g) {r : ℕ}
    {T : CovariantTensorEvaluation n M r} (hT : IsSmoothCovariantTensor T)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    D.hessian (fun y => (g.tensorNorm T y) ^ 2) x u v =
      2 * (∑ a : Fin r → Fin d,
        T x (fun i => b (a i)) *
          D.iteratedCovariantTensorDerivative T 2 x
            (Fin.cons u (Fin.cons v (fun i => b (a i))))) +
      2 * (∑ a : Fin r → Fin d,
        D.covariantTensorDerivative T x (Fin.cons u (fun i => b (a i))) *
          D.covariantTensorDerivative T x (Fin.cons v (fun i => b (a i)))) := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let w (a : Fin r → Fin d) : Fin r → TangentSpace (𝓡 n) x := fun i => b (a i)
  let w0 : Fin 0 → TangentSpace (𝓡 n) x := ![]
  let A : CovariantTensorEvaluation n M (0 + r * 2) :=
    tensorRankCast (Nat.zero_add (r * 2)).symm (pairedProduct T T)
  have hA : IsSmoothCovariantTensor A :=
    isSmoothCovariantTensor_rankCast _ (isSmoothCovariantTensor_pairedProduct hT hT)
  have hScalar : tensorPairTrace (p := 0) (r := r) g A =
      scalarTensor (fun y => (g.tensorNorm T y) ^ 2) := by
    change tensorPairTrace (p := 0) (r := r) g
      (tensorRankCast (Nat.zero_add (r * 2)).symm (pairedProduct T T)) = _
    rw [tensorPairTrace_pairedProduct]
    exact congrArg (scalarTensor (n := n))
      (funext fun y => tensorPairing_self g T y)
  change D.hessian (fun y => (g.tensorNorm T y) ^ 2) x u v =
    2 * (∑ a : Fin r → Fin d,
      T x (w a) * D.iteratedCovariantTensorDerivative T 2 x
        (Fin.cons u (Fin.cons v (w a)))) +
    2 * (∑ a : Fin r → Fin d,
      D.covariantTensorDerivative T x (Fin.cons u (w a)) *
        D.covariantTensorDerivative T x (Fin.cons v (w a)))
  calc
    _ = ∑ a : Fin r → Fin d,
        D.iteratedCovariantTensorDerivative A 2 x
          (Fin.cons u (Fin.cons v (Fin.append w0 (pairedDiagonal (w a))))) := by
      have h := second_covariantTensorDerivative_tensorPairTrace
        (p := 0) (r := r) D hA x u v w0
      rw [hScalar, second_derivative_scalarTensor] at h
      exact h
    _ = ∑ a : Fin r → Fin d,
        (2 * (T x (w a) * D.iteratedCovariantTensorDerivative T 2 x
          (Fin.cons u (Fin.cons v (w a)))) +
        2 * (D.covariantTensorDerivative T x (Fin.cons u (w a)) *
          D.covariantTensorDerivative T x (Fin.cons v (w a)))) := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [A]
      rw [second_derivative_rankCast, append_zero_cast,
        second_covariantTensorDerivative_pairedProduct D hT hT]
      simp only [pairedDiagonal_component]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem tensorNorm_sq_succ (g : RiemannianMetric n M) {r : ℕ}
    (A : CovariantTensorEvaluation n M (r + 1)) (x : M) :
    let b := g.orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    (g.tensorNorm A x) ^ 2 =
      ∑ i : Fin d, ∑ a : Fin r → Fin d,
        (A x (Fin.cons (b i) (fun j => b (a j)))) ^ 2 := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let f (a : Fin (r + 1) → Fin d) := (A x (fun j => b (a j))) ^ 2
  change (Real.sqrt (∑ a : Fin (r + 1) → Fin d, f a)) ^ 2 = _
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  let e := Fin.consEquiv (fun _ : Fin (r + 1) => Fin d)
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  change (A x (fun j => b ((Fin.cons i a : Fin (r + 1) → Fin d) j))) ^ 2 = _
  have he : (fun j => b ((Fin.cons i a : Fin (r + 1) → Fin d) j)) =
      (Fin.cons (b i) (fun j => b (a j)) : Fin (r + 1) → TangentSpace (𝓡 n) x) :=
    Fin.comp_cons b i a
  rw [he]

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem laplacian_tensorNorm_sq (D : LeviCivitaData g) {r : ℕ}
    {T : CovariantTensorEvaluation n M r} (hT : IsSmoothCovariantTensor T)
    (x : M) :
    D.laplacian (fun y => (g.tensorNorm T y) ^ 2) x =
      2 * tensorPairing g T (D.tensorLaplacian T) x +
      2 * (g.tensorNorm (D.covariantTensorDerivative T) x) ^ 2 := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let w (a : Fin r → Fin d) : Fin r → TangentSpace (𝓡 n) x := fun j => b (a j)
  change (∑ i : Fin d, D.hessian (fun y => (g.tensorNorm T y) ^ 2) x (b i) (b i)) = _
  calc
    _ = ∑ i : Fin d,
        (2 * (∑ a : Fin r → Fin d,
          T x (w a) * D.iteratedCovariantTensorDerivative T 2 x
            (Fin.cons (b i) (Fin.cons (b i) (w a)))) +
        2 * (∑ a : Fin r → Fin d,
          (D.covariantTensorDerivative T x (Fin.cons (b i) (w a))) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [pow_two] using hessian_tensorNorm_sq D hT x (b i) (b i)
    _ = 2 * (∑ a : Fin r → Fin d,
        T x (w a) * (∑ i : Fin d, D.iteratedCovariantTensorDerivative T 2 x
          (Fin.cons (b i) (Fin.cons (b i) (w a))))) +
        2 * (∑ i : Fin d, ∑ a : Fin r → Fin d,
          (D.covariantTensorDerivative T x (Fin.cons (b i) (w a))) ^ 2) := by
      rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]
      have hfirst : (∑ i : Fin d, ∑ a : Fin r → Fin d,
          T x (w a) * D.iteratedCovariantTensorDerivative T 2 x
            (Fin.cons (b i) (Fin.cons (b i) (w a)))) =
          ∑ a : Fin r → Fin d,
            T x (w a) * (∑ i : Fin d, D.iteratedCovariantTensorDerivative T 2 x
              (Fin.cons (b i) (Fin.cons (b i) (w a)))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      rw [hfirst]
    _ = _ := by
      have hnorm := tensorNorm_sq_succ g (D.covariantTensorDerivative T) x
      change (g.tensorNorm (D.covariantTensorDerivative T) x) ^ 2 =
        ∑ i : Fin d, ∑ a : Fin r → Fin d,
          (D.covariantTensorDerivative T x (Fin.cons (b i) (w a))) ^ 2 at hnorm
      rw [← hnorm]
      rfl

end PoincareConjecture.RicciFlowAnalysis
