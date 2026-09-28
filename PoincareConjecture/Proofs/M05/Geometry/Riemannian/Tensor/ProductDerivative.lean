import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Product
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.RicciDerivative
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Trace
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.TraceRegularity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Algebra
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Linearity

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma covariantTensorDerivative_tensorProduct
    {k l : ℕ} (D : LeviCivitaData g)
    {S : CovariantTensorEvaluation n M k} {T : CovariantTensorEvaluation n M l}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (u : TangentSpace (𝓡 n) x)
    (v : Fin (k + l) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (tensorProduct S T) x (Fin.cons u v) =
      D.covariantTensorDerivative S x
          (Fin.cons u (fun i => v (Fin.castAdd l i))) *
        T x (fun j => v (Fin.natAdd k j)) +
      S x (fun i => v (Fin.castAdd l i)) *
        D.covariantTensorDerivative T x
          (Fin.cons u (fun j => v (Fin.natAdd k j))) := by
  classical
  let X := fun z : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
  have hSx := hS.contMDiffAt_extend x (fun i => v (Fin.castAdd l i))
  have hTx := hT.contMDiffAt_extend x (fun j => v (Fin.natAdd k j))
  have hderiv := mvfderiv_tensorProduct_extend hS hT x v u
  simp only [covariantTensorDerivative, tensorProduct, Fin.cons_zero, Fin.cons_succ] at hderiv ⊢
  rw [hderiv]
  simp only [Fin.sum_univ_add]
  have hcast (i : Fin k) (q : Fin k) (z : TangentSpace (𝓡 n) x) :
      (Function.update v (Fin.castAdd l i) z) (Fin.castAdd l q) =
        (Function.update (fun r => v (Fin.castAdd l r)) i z) q := by
    by_cases h : q = i
    · subst q; simp
    · have h' : Fin.castAdd l i ≠ Fin.castAdd l q := by
        intro hh
        exact h (Fin.castAdd_injective k l hh.symm)
      simp [Function.update_of_ne h', h]
  have hnat (i : Fin l) (q : Fin l) (z : TangentSpace (𝓡 n) x) :
      (Function.update v (Fin.natAdd k i) z) (Fin.natAdd k q) =
        (Function.update (fun r => v (Fin.natAdd k r)) i z) q := by
    by_cases h : q = i
    · subst q; simp
    · have h' : Fin.natAdd k i ≠ Fin.natAdd k q := by
        intro hh
        exact h (Fin.natAdd_injective l k hh.symm)
      simp [Function.update_of_ne h', h]
  have hcross₁ (i : Fin k) (j : Fin l) :
      Fin.natAdd k j ≠ Fin.castAdd l i := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  have hcross₂ (i : Fin l) (j : Fin k) :
      Fin.castAdd l j ≠ Fin.natAdd k i := by
    intro h
    exact hcross₁ j i h.symm
  have hfirst (i : Fin k) :
      (fun q => Function.update v (Fin.castAdd l i)
        ((D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (v (Fin.castAdd l i))) x) u) (Fin.castAdd l q)) =
      Function.update (fun q => v (Fin.castAdd l q)) i
        ((D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (v (Fin.castAdd l i))) x) u) := by
    funext q
    exact hcast i q _
  have hsecond (i : Fin l) :
      (fun q => Function.update v (Fin.natAdd k i)
        ((D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (v (Fin.natAdd k i))) x) u) (Fin.natAdd k q)) =
      Function.update (fun q => v (Fin.natAdd k q)) i
        ((D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (v (Fin.natAdd k i))) x) u) := by
    funext q
    exact hnat i q _
  have hcrossT (i : Fin k) :
      (fun j => Function.update v (Fin.castAdd l i)
        ((D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (v (Fin.castAdd l i))) x) u) (Fin.natAdd k j)) =
      (fun j => v (Fin.natAdd k j)) := by
    funext j
    simp [Function.update_of_ne (hcross₁ i j)]
  have hcrossS (i : Fin l) :
      (fun j => Function.update v (Fin.natAdd k i)
        ((D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (v (Fin.natAdd k i))) x) u) (Fin.castAdd l j)) =
      (fun j => v (Fin.castAdd l j)) := by
    funext j
    simp [Function.update_of_ne (hcross₂ i j)]
  simp_rw [hfirst, hcrossT, hsecond, hcrossS]
  simp only [smul_eq_mul, FiberBundle.extend_apply_self]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma covariantTensorDerivative_tensorProduct_trace_order_two
    (D : LeviCivitaData g)
    {S T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative
        (fun y z => ∑ i, S y ![z 0, (g.orthonormalBasis y i)] *
          T y ![(g.orthonormalBasis y i), z 1]) x ![a, b, c] =
      ∑ i, (D.covariantTensorDerivative S x
          ![a, b, g.orthonormalBasis x i] * T x ![g.orthonormalBasis x i, c] +
        S x ![b, g.orthonormalBasis x i] *
          D.covariantTensorDerivative T x
            ![a, g.orthonormalBasis x i, c]) := by
  let σ : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective ![2, 0, 1, 3] (by decide)
  have hP := isSmoothCovariantTensor_tensorProduct hS hT
  have htrace := D.covariantTensorDerivative_tensorTrace (hP.perm σ) x a ![b, c]
  simp only [Matrix.Fin.cons_vecCons] at htrace
  have hC :
      g.tensorTrace (fun y (w : Fin 4 → TangentSpace (𝓡 n) y) => tensorProduct S T y (w ∘ σ)) =
        (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) => ∑ i, S y ![z 0, (g.orthonormalBasis y i)] *
          T y ![(g.orthonormalBasis y i), z 1]) := by
    funext y z
    apply Finset.sum_congr rfl
    intro i hi
    have hz :
        (Fin.cons (g.orthonormalBasis y i)
          (Fin.cons (g.orthonormalBasis y i) z)) ∘ σ =
          ![z 0, g.orthonormalBasis y i, g.orthonormalBasis y i, z 1] := by
      ext j
      fin_cases j <;> rfl
    change tensorProduct S T y
      ((Fin.cons (g.orthonormalBasis y i)
        (Fin.cons (g.orthonormalBasis y i) z)) ∘ σ) = _
    rw [hz]
    simp only [tensorProduct]
    congr 1
    · congr 1
      ext j
      fin_cases j <;> rfl
    · congr 1
      ext j
      fin_cases j <;> rfl
  rw [← hC, htrace]
  apply Finset.sum_congr rfl
  intro i hi
  rw [D.covariantTensorDerivative_reindex]
  have heq : Fin.cons a (fun j : Fin 4 =>
      ![a, g.orthonormalBasis x i, g.orthonormalBasis x i, b, c]
        (σ j).succ) =
      ![a, b, g.orthonormalBasis x i, g.orthonormalBasis x i, c] := by
    ext j
    fin_cases j <;> rfl
  change D.covariantTensorDerivative (tensorProduct S T) x
      (Fin.cons a (fun j : Fin 4 =>
        ![a, g.orthonormalBasis x i, g.orthonormalBasis x i, b, c]
          (σ j).succ)) = _
  rw [heq]
  have hp := D.covariantTensorDerivative_tensorProduct hS hT x a
    ![b, g.orthonormalBasis x i, g.orthonormalBasis x i, c]
  simp only [Matrix.Fin.cons_vecCons] at hp
  rw [hp]
  have hsvec : (fun j : Fin 2 =>
      ![b, g.orthonormalBasis x i, g.orthonormalBasis x i, c]
        (Fin.castAdd 2 j)) = ![b, g.orthonormalBasis x i] := by
    funext j
    fin_cases j <;> rfl
  have htvec : (fun j : Fin 2 =>
      ![b, g.orthonormalBasis x i, g.orthonormalBasis x i, c]
        (Fin.natAdd 2 j)) = ![g.orthonormalBasis x i, c] := by
    funext j
    fin_cases j <;> rfl
  rw [hsvec, htvec]
  have hcons1 : Fin.cons a ![b, g.orthonormalBasis x i] =
      ![a, b, g.orthonormalBasis x i] := by
    ext j; fin_cases j <;> rfl
  have hcons2 : Fin.cons a ![g.orthonormalBasis x i, c] =
      ![a, g.orthonormalBasis x i, c] := by
    ext j; fin_cases j <;> rfl
  rw [hcons1, hcons2]

lemma isSmoothCovariantTensor_tensorProduct_trace_order_two
    (D : LeviCivitaData g)
    {S T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) =>
      ∑ i, S y ![z 0, (g.orthonormalBasis y i)] *
        T y ![(g.orthonormalBasis y i), z 1]) := by
  let σ : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective ![2, 0, 1, 3] (by decide)
  have hP := isSmoothCovariantTensor_tensorProduct hS hT
  have hC :
      g.tensorTrace (fun y (w : Fin 4 → TangentSpace (𝓡 n) y) => tensorProduct S T y (w ∘ σ)) =
        (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) => ∑ i, S y ![z 0, (g.orthonormalBasis y i)] *
          T y ![(g.orthonormalBasis y i), z 1]) := by
    funext y z
    apply Finset.sum_congr rfl
    intro i hi
    have hz :
        (Fin.cons (g.orthonormalBasis y i)
          (Fin.cons (g.orthonormalBasis y i) z)) ∘ σ =
          ![z 0, g.orthonormalBasis y i, g.orthonormalBasis y i, z 1] := by
      ext j
      fin_cases j <;> rfl
    change tensorProduct S T y
      ((Fin.cons (g.orthonormalBasis y i)
        (Fin.cons (g.orthonormalBasis y i) z)) ∘ σ) = _
    rw [hz]
    simp only [tensorProduct]
    congr 1
    · congr 1
      ext j
      fin_cases j <;> rfl
    · congr 1
      ext j
      fin_cases j <;> rfl
  rw [← hC]
  exact (hP.perm σ).tensorTrace

end PoincareConjecture.LeviCivitaData
