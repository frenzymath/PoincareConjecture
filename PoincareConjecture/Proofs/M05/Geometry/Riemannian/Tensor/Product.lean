
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private def finSumFinEquiv (k l : ℕ) : Fin k ⊕ Fin l ≃ Fin (k + l) :=
  { toFun := Sum.elim (Fin.castAdd l) (Fin.natAdd k)
    invFun := @Fin.addCases k l (fun _ => Fin k ⊕ Fin l) Sum.inl Sum.inr
    left_inv := by rintro (_ | _) <;> simp
    right_inv := by refine Fin.addCases (fun i => ?_) (fun i => ?_) <;> simp }


def tensorProduct {k l : ℕ} (S : CovariantTensorEvaluation n M k)
    (T : CovariantTensorEvaluation n M l) : CovariantTensorEvaluation n M (k + l) :=
  fun x v ↦ S x (fun i ↦ v (Fin.castAdd l i)) * T x (fun j ↦ v (Fin.natAdd k j))

@[simp] lemma tensorProduct_apply {k l : ℕ}
    (S : CovariantTensorEvaluation n M k) (T : CovariantTensorEvaluation n M l)
    (x : M) (v : Fin (k + l) → TangentSpace (𝓡 n) x) :
    tensorProduct S T x v = S x (fun i ↦ v (Fin.castAdd l i)) * T x (fun j ↦ v (Fin.natAdd k j)) := rfl

def tensorProductWitness {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {k l : ℕ} (A : MultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ)
    (B : MultilinearMap ℝ (fun _ : Fin l ↦ E) ℝ) :
    MultilinearMap ℝ (fun _ : Fin (k + l) ↦ E) ℝ := by
  let C : MultilinearMap ℝ (fun i : Fin (k + l) ↦ E) ℝ :=
    { toFun := fun v ↦ A (fun i ↦ v (Fin.castAdd l i)) * B (fun j ↦ v (Fin.natAdd k j))
      map_update_add' {hDecEq} := by
        intro v i a b
        refine Fin.addCases (m := k) (n := l) ?_ ?_ i
        · intro j
          have hA (z : E) : (fun q ↦ Function.update v (Fin.castAdd l j) z
              (Fin.castAdd l q)) = Function.update (fun q ↦ v (Fin.castAdd l q)) j z := by
            ext q
            by_cases h : q = j <;> simp [h]
          have hB (z : E) : (fun q ↦ Function.update v (Fin.castAdd l j) z
              (Fin.natAdd k q)) = (fun q ↦ v (Fin.natAdd k q)) := by
            ext q
            have hq : Fin.natAdd k q ≠ Fin.castAdd l j := by
              intro h
              have hh := congrArg Fin.val h
              simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
              omega
            simp [hq]
          rw [hA (a + b), hB (a + b), A.map_update_add, hA a, hB a, hA b, hB b]
          ring
        · intro j
          have hA (z : E) : (fun q ↦ Function.update v (Fin.natAdd k j) z
              (Fin.castAdd l q)) = (fun q ↦ v (Fin.castAdd l q)) := by
            ext q
            have hq : Fin.castAdd l q ≠ Fin.natAdd k j := by
              intro h
              have hh := congrArg Fin.val h
              simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
              omega
            simp [hq]
          have hB (z : E) : (fun q ↦ Function.update v (Fin.natAdd k j) z
              (Fin.natAdd k q)) = Function.update (fun q ↦ v (Fin.natAdd k q)) j z := by
            ext q
            by_cases h : q = j <;> simp [h]
          rw [hA (a + b), hB (a + b), B.map_update_add, hA a, hB a, hA b, hB b]
          ring
      map_update_smul' {hDecEq} := by
        intro v i c a
        refine Fin.addCases (m := k) (n := l) ?_ ?_ i
        · intro j
          have hA (z : E) : (fun q ↦ Function.update v (Fin.castAdd l j) z
              (Fin.castAdd l q)) = Function.update (fun q ↦ v (Fin.castAdd l q)) j z := by
            ext q
            by_cases h : q = j <;> simp [h]
          have hB (z : E) : (fun q ↦ Function.update v (Fin.castAdd l j) z
              (Fin.natAdd k q)) = (fun q ↦ v (Fin.natAdd k q)) := by
            ext q
            have hq : Fin.natAdd k q ≠ Fin.castAdd l j := by
              intro h
              have hh := congrArg Fin.val h
              simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
              omega
            simp [hq]
          rw [hA (c • a), hB (c • a), A.map_update_smul, hA a, hB a]
          simp [smul_eq_mul]
          ring
        · intro j
          have hA (z : E) : (fun q ↦ Function.update v (Fin.natAdd k j) z
              (Fin.castAdd l q)) = (fun q ↦ v (Fin.castAdd l q)) := by
            ext q
            have hq : Fin.castAdd l q ≠ Fin.natAdd k j := by
              intro h
              have hh := congrArg Fin.val h
              simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
              omega
            simp [hq]
          have hB (z : E) : (fun q ↦ Function.update v (Fin.natAdd k j) z
              (Fin.natAdd k q)) = Function.update (fun q ↦ v (Fin.natAdd k q)) j z := by
            ext q
            by_cases h : q = j <;> simp [h]
          rw [hA (c • a), hB (c • a), B.map_update_smul, hA a, hB a]
          simp [smul_eq_mul]
          ring
      }
  exact C

lemma isSmoothCovariantTensor_tensorProduct {k l : ℕ}
    {S : CovariantTensorEvaluation n M k} {T : CovariantTensorEvaluation n M l}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (tensorProduct S T) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hS.1 x
    obtain ⟨B, hB⟩ := hT.1 x
    refine ⟨tensorProductWitness (E := TangentSpace (𝓡 n) x) (k := k) (l := l) A B, ?_⟩
    intro v
    change S x (fun i ↦ v (Fin.castAdd l i)) * T x (fun j ↦ v (Fin.natAdd k j)) = _
    simp [tensorProductWitness, MultilinearMap.domDomCongr, finSumFinEquiv,
      MultilinearMap.compMultilinearMap_apply, MultilinearMap.mkPiRing_apply,
      hA, hB, Fin.append]
  · intro U hU X hX
    letI : ContMDiffRing (𝓘(ℝ, ℝ)) ∞ ℝ := instFieldContMDiffRing
    have hSX : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
        (fun y ↦ S y (fun i ↦ X (Fin.castAdd l i) y)) U :=
      hS.2 U hU (fun i y ↦ X (Fin.castAdd l i) y) (fun i ↦ hX (Fin.castAdd l i))
    have hTX : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
        (fun y ↦ T y (fun j ↦ X (Fin.natAdd k j) y)) U :=
      hT.2 U hU (fun j y ↦ X (Fin.natAdd k j) y) (fun j ↦ hX (Fin.natAdd k j))
    exact hSX.mul hTX

lemma mvfderiv_tensorProduct_extend {k l : ℕ}
    {S : CovariantTensorEvaluation n M k} {T : CovariantTensorEvaluation n M l}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin (k + l) → TangentSpace (𝓡 n) x)
    (w : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n)
        (fun y ↦ tensorProduct S T y
          (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)) x w =
      S x (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v (Fin.castAdd l i)) x) •
        mvfderiv (𝓡 n)
          (fun y ↦ T y (fun j ↦ FiberBundle.extend
            (EuclideanSpace ℝ (Fin n)) (v (Fin.natAdd k j)) y)) x w +
      T x (fun j ↦ FiberBundle.extend
          (EuclideanSpace ℝ (Fin n)) (v (Fin.natAdd k j)) x) •
        mvfderiv (𝓡 n)
          (fun y ↦ S y (fun i ↦ FiberBundle.extend
            (EuclideanSpace ℝ (Fin n)) (v (Fin.castAdd l i)) y)) x w := by
  have hSx := hS.contMDiffAt_extend x (fun i ↦ v (Fin.castAdd l i))
  have hTx := hT.contMDiffAt_extend x (fun j ↦ v (Fin.natAdd k j))
  unfold tensorProduct
  have hm := mvfderiv_fun_mul (hSx.mdifferentiableAt (by simp))
    (hTx.mdifferentiableAt (by simp))
  simpa [smul_eq_mul] using congrArg (fun L ↦ L w) hm

end PoincareConjecture
