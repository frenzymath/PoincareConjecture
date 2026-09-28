import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace.Double
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.ProductDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma curvature_three_eq_double_trace (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) :
    (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 1)
        (g.orthonormalBasis y j) * T y ![g.orthonormalBasis y i, g.orthonormalBasis y j, z 2]) =
    g.tensorTrace (g.tensorTrace (fun y z => tensorProduct D.riemannEvaluation T y
      (z ∘ (Equiv.ofBijective ![4, 0, 5, 2, 1, 3, 6] (by decide))))) := by
  funext y z
  symm
  let e := g.orthonormalBasis y
  let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective ![4, 0, 5, 2, 1, 3, 6] (by decide)
  simp only [RiemannianMetric.tensorTrace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hz : (Fin.cons (e i) (Fin.cons (e i) (Fin.cons (e j) (Fin.cons (e j) z))) :
      Fin 7 → TangentSpace (𝓡 n) y) ∘ σ =
      ![z 0, e i, z 1, e j, e i, e j, z 2] := by ext q; fin_cases q <;> rfl
  change tensorProduct D.riemannEvaluation T y
    ((Fin.cons (e i) (Fin.cons (e i) (Fin.cons (e j) (Fin.cons (e j) z))) :
      Fin 7 → TangentSpace (𝓡 n) y) ∘ σ) = _
  rw [hz]
  change D.curvatureTensor y (z 0) (e i) (z 1) (e j) *
    T y (fun q => ![z 0, e i, z 1, e j, e i, e j, z 2] (Fin.natAdd 4 q)) = _
  congr 1
  congr 1
  ext q; fin_cases q <;> rfl

lemma isSmoothCovariantTensor_curvature_three
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 1)
        (g.orthonormalBasis y j) * T y ![g.orthonormalBasis y i, g.orthonormalBasis y j, z 2]) := by
  rw [D.curvature_three_eq_double_trace]
  exact ((isSmoothCovariantTensor_tensorProduct hD.1 hT).perm _).tensorTrace.tensorTrace

lemma covariantTensorDerivative_curvature_three
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    D.covariantTensorDerivative (fun y z =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 1)
        (g.orthonormalBasis y j) * T y ![g.orthonormalBasis y i, g.orthonormalBasis y j, z 2])
      x ![p, a, b, c] =
      ∑ i, ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![p, a, e i, b, e j] *
        T x ![e i, e j, c] + D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative T x ![p, e i, e j, c]) := by
  let e := g.orthonormalBasis x
  let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective ![4, 0, 5, 2, 1, 3, 6] (by decide)
  let S := fun y z => tensorProduct D.riemannEvaluation T y (z ∘ σ)
  have hS : IsSmoothCovariantTensor S := (isSmoothCovariantTensor_tensorProduct hD.1 hT).perm σ
  rw [D.curvature_three_eq_double_trace]
  have h := D.covariantTensorDerivative_tensorTrace_tensorTrace hS x p ![a, b, c]
  simp only [Matrix.Fin.cons_vecCons] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change D.covariantTensorDerivative S x ![p, e i, e i, e j, e j, a, b, c] = _
  dsimp only [S]
  rw [D.covariantTensorDerivative_reindex]
  have hz : Fin.cons p (fun q : Fin 7 => ![p, e i, e i, e j, e j, a, b, c] (σ q).succ) =
      ![p, a, e i, b, e j, e i, e j, c] := by ext q; fin_cases q <;> rfl
  change D.covariantTensorDerivative (tensorProduct D.riemannEvaluation T) x
    (Fin.cons p (fun q : Fin 7 => ![p, e i, e i, e j, e j, a, b, c] (σ q).succ)) = _
  rw [hz]
  have hp := D.covariantTensorDerivative_tensorProduct hD.1 hT x p ![a, e i, b, e j, e i, e j, c]
  simp only [Matrix.Fin.cons_vecCons] at hp
  rw [hp]
  have hv₁ : (fun q : Fin 4 => ![a, e i, b, e j, e i, e j, c] (Fin.castAdd 3 q)) =
      ![a, e i, b, e j] := by ext q; fin_cases q <;> rfl
  have hv₂ : (fun q : Fin 3 => ![a, e i, b, e j, e i, e j, c] (Fin.natAdd 4 q)) =
      ![e i, e j, c] := by ext q; fin_cases q <;> rfl
  rw [hv₁, hv₂]
  rfl

private lemma curvature_three_middle_perm (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) :
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 2)
        (g.orthonormalBasis y j) * T y ![g.orthonormalBasis y i, z 1, g.orthonormalBasis y j]) =
    (fun y z => (fun w => ∑ i, ∑ j, D.curvatureTensor y (w 0) (g.orthonormalBasis y i) (w 1)
      (g.orthonormalBasis y j) * T y (![g.orthonormalBasis y i, g.orthonormalBasis y j, w 2] ∘ σ))
        (z ∘ σ)) := by
  dsimp only
  funext y z
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  norm_num
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  congr 1
  ext q
  fin_cases q <;> norm_num [Equiv.swap_apply_def] <;> rfl

lemma isSmoothCovariantTensor_curvature_three_middle
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 2)
        (g.orthonormalBasis y j) * T y ![g.orthonormalBasis y i, z 1, g.orthonormalBasis y j]) := by
  rw [D.curvature_three_middle_perm]
  exact (D.isSmoothCovariantTensor_curvature_three hD (hT.perm (Equiv.swap 1 2))).perm
    (Equiv.swap 1 2)

lemma covariantTensorDerivative_curvature_three_middle
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    D.covariantTensorDerivative (fun y z =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 2)
        (g.orthonormalBasis y j) * T y ![g.orthonormalBasis y i, z 1, g.orthonormalBasis y j])
      x ![p, a, b, c] =
      ∑ i, ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![p, a, e i, c, e j] *
        T x ![e i, b, e j] + D.curvatureTensor x a (e i) c (e j) *
        D.covariantTensorDerivative T x ![p, e i, b, e j]) := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let S : CovariantTensorEvaluation n M 3 := fun y w =>
    ∑ i, ∑ j, D.curvatureTensor y (w 0) (g.orthonormalBasis y i) (w 1)
      (g.orthonormalBasis y j) * T y (![g.orthonormalBasis y i, g.orthonormalBasis y j, w 2] ∘ σ)
  have hσ (v w z : TangentSpace (𝓡 n) x) : ![v, w, z] ∘ σ = ![v, z, w] := by
    ext q; fin_cases q <;> simp [σ, Equiv.swap_apply_def]
  have hdσ (v w z : TangentSpace (𝓡 n) x) :
      Fin.cons p (fun q : Fin 3 => ![p, v, w, z] (σ q).succ) = ![p, v, z, w] := by
    ext q; fin_cases q <;> simp [σ, Fin.cons, Equiv.swap_apply_def] <;> rfl
  rw [D.curvature_three_middle_perm]
  change D.covariantTensorDerivative (fun y z => S y (z ∘ σ)) x ![p, a, b, c] = _
  rw [D.covariantTensorDerivative_reindex]
  change D.covariantTensorDerivative _ x
    (Fin.cons p (fun q : Fin 3 => ![p, a, b, c] (σ q).succ)) = _
  rw [hdσ, D.covariantTensorDerivative_curvature_three hD (hT.perm σ)]
  simp_rw [hσ, D.covariantTensorDerivative_reindex]
  simp only [Matrix.cons_val_zero]
  simp_rw [hdσ]

private lemma curvature_three_last_perm (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) :
    let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective ![1, 2, 0] (by decide)
    let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective ![2, 0, 1] (by decide)
    (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, D.curvatureTensor y (z 1) (g.orthonormalBasis y i) (z 2)
        (g.orthonormalBasis y j) * T y ![z 0, g.orthonormalBasis y i, g.orthonormalBasis y j]) =
    (fun y z => (fun w => ∑ i, ∑ j, D.curvatureTensor y (w 0) (g.orthonormalBasis y i) (w 1)
      (g.orthonormalBasis y j) * T y (![g.orthonormalBasis y i, g.orthonormalBasis y j, w 2] ∘ τ))
        (z ∘ σ)) := by
  dsimp only
  funext y z
  simp only [Function.comp_apply, Equiv.coe_ofBijective,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  congr 1
  ext q
  fin_cases q <;> simp

lemma isSmoothCovariantTensor_curvature_three_last
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, D.curvatureTensor y (z 1) (g.orthonormalBasis y i) (z 2)
        (g.orthonormalBasis y j) * T y ![z 0, g.orthonormalBasis y i, g.orthonormalBasis y j]) := by
  rw [D.curvature_three_last_perm]
  exact (D.isSmoothCovariantTensor_curvature_three hD (hT.perm _)).perm _

lemma covariantTensorDerivative_curvature_three_last
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    D.covariantTensorDerivative (fun y z =>
      ∑ i, ∑ j, D.curvatureTensor y (z 1) (g.orthonormalBasis y i) (z 2)
        (g.orthonormalBasis y j) * T y ![z 0, g.orthonormalBasis y i, g.orthonormalBasis y j])
      x ![p, a, b, c] =
      ∑ i, ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![p, b, e i, c, e j] *
        T x ![a, e i, e j] + D.curvatureTensor x b (e i) c (e j) *
        D.covariantTensorDerivative T x ![p, a, e i, e j]) := by
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective ![1, 2, 0] (by decide)
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective ![2, 0, 1] (by decide)
  let S : CovariantTensorEvaluation n M 3 := fun y w =>
    ∑ i, ∑ j, D.curvatureTensor y (w 0) (g.orthonormalBasis y i) (w 1)
      (g.orthonormalBasis y j) * T y (![g.orthonormalBasis y i, g.orthonormalBasis y j, w 2] ∘ τ)
  have hτ (v w z : TangentSpace (𝓡 n) x) : ![v, w, z] ∘ τ = ![z, v, w] := by
    ext q; fin_cases q <;> simp [τ]
  have hdσ (v w z : TangentSpace (𝓡 n) x) :
      Fin.cons p (fun q : Fin 3 => ![p, v, w, z] (σ q).succ) = ![p, w, z, v] := by
    ext q; fin_cases q <;> simp [σ, Fin.cons] <;> rfl
  have hdτ (v w z : TangentSpace (𝓡 n) x) :
      Fin.cons p (fun q : Fin 3 => ![p, v, w, z] (τ q).succ) = ![p, z, v, w] := by
    ext q; fin_cases q <;> simp [τ, Fin.cons] <;> rfl
  rw [D.curvature_three_last_perm]
  change D.covariantTensorDerivative (fun y z => S y (z ∘ σ)) x ![p, a, b, c] = _
  rw [D.covariantTensorDerivative_reindex]
  change D.covariantTensorDerivative _ x
    (Fin.cons p (fun q : Fin 3 => ![p, a, b, c] (σ q).succ)) = _
  rw [hdσ, D.covariantTensorDerivative_curvature_three hD (hT.perm τ)]
  simp_rw [hτ, D.covariantTensorDerivative_reindex]
  simp only [Matrix.cons_val_zero]
  simp_rw [hdτ]

end PoincareConjecture.LeviCivitaData
