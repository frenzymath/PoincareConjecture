import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatTrace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

private noncomputable def productTwoDerivativePerm : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective ![1, 2, 0, 3, 4] (by decide)

private lemma productTwoDerivative_eq (D : LeviCivitaData g)
    {S T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    D.covariantTensorDerivative (tensorProduct S T) = fun x v =>
      tensorProduct (D.covariantTensorDerivative S) T x v +
      tensorProduct S (D.covariantTensorDerivative T) x (v ∘ productTwoDerivativePerm) := by
  funext x v
  have hv : v = Fin.cons (v 0) (fun i : Fin 4 => v i.succ) := by
    ext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv]
  rw [D.covariantTensorDerivative_tensorProduct hS hT]
  simp only [tensorProduct]
  congr 2 <;> congr 1 <;> ext i <;> fin_cases i <;> rfl

lemma LeviCivitaData.tensorLaplacian_tensorProduct_two_two
    (D : LeviCivitaData g) {S T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hDS : IsSmoothCovariantTensor (D.covariantTensorDerivative S))
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T))
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (tensorProduct S T) x ![a,b,c,d] =
      D.tensorLaplacian S x ![a,b] * T x ![c,d] +
      S x ![a,b] * D.tensorLaplacian T x ![c,d] +
      2 * ∑ i, D.covariantTensorDerivative S x ![g.orthonormalBasis x i,a,b] *
        D.covariantTensorDerivative T x ![g.orthonormalBasis x i,c,d] := by
  have hsecond (u w : TangentSpace (𝓡 n) x) :
      D.iteratedCovariantTensorDerivative (tensorProduct S T) 2 x ![u,w,a,b,c,d] =
        D.iteratedCovariantTensorDerivative S 2 x ![u,w,a,b] * T x ![c,d] +
        D.covariantTensorDerivative S x ![w,a,b] *
          D.covariantTensorDerivative T x ![u,c,d] +
        (D.covariantTensorDerivative S x ![u,a,b] *
          D.covariantTensorDerivative T x ![w,c,d] +
        S x ![a,b] * D.iteratedCovariantTensorDerivative T 2 x ![u,w,c,d]) := by
    simp only [LeviCivitaData.iteratedCovariantTensorDerivative]
    rw [productTwoDerivative_eq D hS hT,
      D.covariantTensorDerivative_add (isSmoothCovariantTensor_tensorProduct hDS hT)
        ((isSmoothCovariantTensor_tensorProduct hS hDT).perm productTwoDerivativePerm)]
    dsimp only
    rw [D.covariantTensorDerivative_reindex]
    have hv : Fin.cons (![u,w,a,b,c,d] 0)
        (fun i => ![u,w,a,b,c,d] (productTwoDerivativePerm i).succ) = ![u,a,b,w,c,d] := by
      ext i
      fin_cases i <;> rfl
    rw [hv]
    have h₁ := D.covariantTensorDerivative_tensorProduct hDS hT x u ![w,a,b,c,d]
    have h₂ := D.covariantTensorDerivative_tensorProduct hS hDT x u ![a,b,w,c,d]
    simp only [Matrix.Fin.cons_vecCons] at h₁ h₂
    rw [h₁, h₂]
    congr 2 <;> congr 1 <;> congr 1 <;> ext i <;> fin_cases i <;> rfl
  simp only [LeviCivitaData.tensorLaplacian, Matrix.Fin.cons_vecCons]
  simp_rw [hsecond]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma RicciFlow.tensorHeatOperator_tensorProduct_two_two
    (F : RicciFlow n M J) {S T : ℝ → CovariantTensorEvaluation n M 2} {t : ℝ}
    (hS : IsSmoothCovariantTensor (S t)) (hT : IsSmoothCovariantTensor (T t))
    (hDS : IsSmoothCovariantTensor ((F.connection t).covariantTensorDerivative (S t)))
    (hDT : IsSmoothCovariantTensor ((F.connection t).covariantTensorDerivative (T t)))
    (hSt : ∀ y z, DifferentiableAt ℝ (fun s => S s y z) t)
    (hTt : ∀ y z, DifferentiableAt ℝ (fun s => T s y z) t)
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    F.tensorHeatOperator (fun s => tensorProduct (S s) (T s)) t x ![a,b,c,d] =
      F.tensorHeatOperator S t x ![a,b] * T t x ![c,d] +
      S t x ![a,b] * F.tensorHeatOperator T t x ![c,d] -
      2 * ∑ i, (F.connection t).covariantTensorDerivative (S t) x
        ![(F.metric t).orthonormalBasis x i,a,b] *
        (F.connection t).covariantTensorDerivative (T t) x
          ![(F.metric t).orthonormalBasis x i,c,d] := by
  have hp (s : ℝ) : tensorProduct (S s) (T s) x ![a,b,c,d] =
      S s x ![a,b] * T s x ![c,d] := by
    unfold tensorProduct
    congr 1 <;> congr 1 <;> ext i <;> fin_cases i <;> rfl
  have ha := (F.connection t).ricciTensorAction_tensorProduct (S t) (T t) x ![a,b,c,d]
  have hv₁ : (fun i : Fin 2 => ![a,b,c,d] (Fin.castAdd 2 i)) = ![a,b] := by
    ext i; fin_cases i <;> rfl
  have hv₂ : (fun i : Fin 2 => ![a,b,c,d] (Fin.natAdd 2 i)) = ![c,d] := by
    ext i; fin_cases i <;> rfl
  rw [hv₁, hv₂] at ha
  simp only [RicciFlow.tensorHeatOperator, hp, deriv_fun_mul (hSt _ _) (hTt _ _), ha,
    LeviCivitaData.tensorLaplacian_tensorProduct_two_two _ hS hT hDS hDT]
  ring

lemma RicciFlow.scalarHeatOperator_tensorTrace_two
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {T W : ℝ → CovariantTensorEvaluation n M 2} {t : ℝ} (ht : t ∈ interior J)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hW : ∀ (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t) (x : M) :
    deriv (fun s => ∑ i, T s x ![(F.metric s).orthonormalBasis x i,
      (F.metric s).orthonormalBasis x i]) t -
      (F.connection t).laplacian (fun y => ∑ i,
        T t y ![(F.metric t).orthonormalBasis y i, (F.metric t).orthonormalBasis y i]) x =
      ∑ i, F.tensorHeatOperator T t x ![(F.metric t).orthonormalBasis x i,
        (F.metric t).orthonormalBasis x i] := by
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  have hD := hC.tensor_calculus n M (F.metric t) D
  have htime := (F.hasDerivAt_tensorTrace ht x hT (hW x) (Fin.elim0)).deriv
  have hlap := D.sum_tensorLaplacian_eq_laplacian_trace (hT t)
    (hD.2.2.1 _ _ (hT t)) x
  have htuple (a c : TangentSpace (𝓡 n) x) : Fin.cons a (Fin.cons c Fin.elim0) = ![a,c] := by
    ext i; fin_cases i <;> rfl
  simp only [RiemannianMetric.tensorTrace, htuple] at htime
  rw [htime, ← hlap]
  simp only [RicciFlow.tensorHeatOperator, (hW _ _).deriv,
    LeviCivitaData.ricciTensorAction_two, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  change (∑ i, W t x ![b i,b i]) +
      2 * (∑ i, ∑ j, D.ricci x (b i) (b j) * T t x ![b i,b j]) - _ = _
  have hs : (∑ i, ∑ j, D.ricci x (b i) (b j) * T t x ![b j,b i]) =
      ∑ i, ∑ j, D.ricci x (b i) (b j) * T t x ![b i,b j] := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(hD.2.2.2.1 x (b j) (b i) (b i) (b j)).2.2.2]
  dsimp only [D, b] at hs
  rw [hs]
  ring

end PoincareConjecture
