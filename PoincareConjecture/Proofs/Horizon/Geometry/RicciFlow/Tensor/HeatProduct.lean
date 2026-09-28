import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Laplacian.Product


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

lemma LeviCivitaData.ricciTensorAction_reindex {k : ℕ} (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M k) (σ : Equiv.Perm (Fin k))
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.ricciTensorAction (fun y w => T y (w ∘ σ)) x v =
      D.ricciTensorAction T x (v ∘ σ) := by
  unfold LeviCivitaData.ricciTensorAction
  rw [← Equiv.sum_comp σ]
  simp only [Function.update_comp_eq_of_injective v σ.injective, Function.comp_apply]

lemma RicciFlow.tensorHeatOperator_reindex {k : ℕ} (F : RicciFlow n M J)
    (T : ℝ → CovariantTensorEvaluation n M k) (σ : Equiv.Perm (Fin k))
    (t : ℝ) (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    F.tensorHeatOperator (fun s y w => T s y (w ∘ σ)) t x v =
      F.tensorHeatOperator T t x (v ∘ σ) := by
  simp only [RicciFlow.tensorHeatOperator, LeviCivitaData.ricciTensorAction_reindex,
    LeviCivitaData.tensorLaplacian_reindex]

lemma LeviCivitaData.ricciTensorAction_tensorProduct {k l : ℕ}
    (D : LeviCivitaData g) (S : CovariantTensorEvaluation n M k)
    (T : CovariantTensorEvaluation n M l)
    (x : M) (v : Fin (k + l) → TangentSpace (𝓡 n) x) :
    D.ricciTensorAction (tensorProduct S T) x v =
      D.ricciTensorAction S x (fun i => v (Fin.castAdd l i)) *
        T x (fun i => v (Fin.natAdd k i)) +
      S x (fun i => v (Fin.castAdd l i)) *
        D.ricciTensorAction T x (fun i => v (Fin.natAdd k i)) := by
  have hne (i : Fin k) (j : Fin l) : Fin.castAdd l i ≠ Fin.natAdd k j := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
    omega
  simp only [LeviCivitaData.ricciTensorAction, tensorProduct, Fin.sum_univ_add,
    Function.update_comp_eq_of_injective' v (Fin.castAdd_injective k l),
    Function.update_comp_eq_of_injective' v (Fin.natAdd_injective l k),
    Function.update_comp_eq_of_forall_ne' v _ (fun j => (hne _ j).symm),
    Function.update_comp_eq_of_forall_ne' v _ (fun i => hne i _),
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

lemma RicciFlow.tensorHeatOperator_tensorProduct_four_two
    (F : RicciFlow n M J)
    {S : ℝ → CovariantTensorEvaluation n M 4}
    {T : ℝ → CovariantTensorEvaluation n M 2} {t : ℝ}
    (hS : IsSmoothCovariantTensor (S t)) (hT : IsSmoothCovariantTensor (T t))
    (hDS : IsSmoothCovariantTensor ((F.connection t).covariantTensorDerivative (S t)))
    (hDT : IsSmoothCovariantTensor ((F.connection t).covariantTensorDerivative (T t)))
    (hSt : ∀ y z, DifferentiableAt ℝ (fun s => S s y z) t)
    (hTt : ∀ y z, DifferentiableAt ℝ (fun s => T s y z) t)
    (x : M) (a b c d e f : TangentSpace (𝓡 n) x) :
    F.tensorHeatOperator (fun s => tensorProduct (S s) (T s)) t x ![a,b,c,d,e,f] =
      F.tensorHeatOperator S t x ![a,b,c,d] * T t x ![e,f] +
      S t x ![a,b,c,d] * F.tensorHeatOperator T t x ![e,f] -
      2 * ∑ i,
        (F.connection t).covariantTensorDerivative (S t) x
          ![(F.metric t).orthonormalBasis x i,a,b,c,d] *
        (F.connection t).covariantTensorDerivative (T t) x
          ![(F.metric t).orthonormalBasis x i,e,f] := by
  have hp (s : ℝ) : tensorProduct (S s) (T s) x ![a,b,c,d,e,f] =
      S s x ![a,b,c,d] * T s x ![e,f] := by
    unfold tensorProduct
    congr 1 <;> congr 1 <;> ext i <;> fin_cases i <;> rfl
  have ha := (F.connection t).ricciTensorAction_tensorProduct (S t) (T t)
    x ![a,b,c,d,e,f]
  have hv₁ : (fun i : Fin 4 => ![a,b,c,d,e,f] (Fin.castAdd 2 i)) = ![a,b,c,d] := by
    ext i; fin_cases i <;> rfl
  have hv₂ : (fun i : Fin 2 => ![a,b,c,d,e,f] (Fin.natAdd 4 i)) = ![e,f] := by
    ext i; fin_cases i <;> rfl
  rw [hv₁, hv₂] at ha
  simp only [RicciFlow.tensorHeatOperator, hp, deriv_fun_mul (hSt _ _) (hTt _ _), ha,
    LeviCivitaData.tensorLaplacian_tensorProduct_four_two _ hS hT hDS hDT]
  ring

end PoincareConjecture
