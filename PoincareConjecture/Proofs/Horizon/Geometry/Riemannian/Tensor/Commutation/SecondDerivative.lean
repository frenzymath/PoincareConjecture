import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.DerivativeOnFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.VectorField.Commutator
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.SlotAlgebra








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma covariantTensorDerivative_cons_update
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (W : Fin k → (y : M) → TangentSpace (𝓡 n) y)
    (Z : (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hW : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (W i)) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Z) x)
    (b : TangentSpace (𝓡 n) x) (i : Fin k) :
    D.covariantTensorDerivative T x
        (Fin.cons b (Function.update (fun j => W j x) i (Z x))) =
      mvfderiv (𝓡 n) (fun y => T y (Function.update (fun j => W j y) i (Z y))) x b -
        ∑ j, T x (Function.update (Function.update (fun l => W l x) i (Z x)) j
          (D.connection (Function.update W i Z j) x b)) := by
  classical
  have heval (y : M) : (fun j => Function.update W i Z j y) =
      Function.update (fun j => W j y) i (Z y) := by
    ext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  have h := D.covariantTensorDerivative_on_fields hT (Function.update W i Z) x
    (fun j => by by_cases h : j = i <;> simp [h, Function.update_of_ne, hW, hZ]) b
  simpa only [heval] using h

private lemma secondCovariantTensorDerivative_expand
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (a b : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
    let W := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)
    let f := fun y => T y (fun i => W i y)
    let C := D.covariantDerivativeOnFields
    D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        (Fin.cons a (Fin.cons b v)) =
      mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (Y y)) x a -
        mvfderiv (𝓡 n) (fun y => ∑ i, T y
          (Function.update (fun j => W j y) i (C Y (W i) y))) x a -
        (mvfderiv (𝓡 n) f x (C X Y x) -
          ∑ i, T x (Function.update v i (D.connection (W i) x (C X Y x)))) -
        ∑ i, (mvfderiv (𝓡 n) (fun y => T y
            (Function.update (fun j => W j y) i (C X (W i) y))) x b -
          ∑ j, T x (Function.update (Function.update v i (C X (W i) x)) j
            (D.connection (Function.update W i (C X (W i)) j) x b))) := by
  classical
  dsimp only
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  let W := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)
  let f := fun y => T y (fun i => W i y)
  have hX := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) a
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) b
  have hW (i : Fin k) :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) (v i)
  have hTW := hT.contMDiffAt_apply hW
  have hCW (i : Fin k) := D.contMDiffAt_covariantDerivativeOnFields hY (hW i)
  have hupdate (i : Fin k) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => T y (Function.update (fun j => W j y) i
        (D.covariantDerivativeOnFields Y (W i) y))) x := by
    have h := hT.contMDiffAt_apply (x := x) (X := Function.update W i
      (D.covariantDerivativeOnFields Y (W i)))
      (fun j => by
        by_cases h : j = i
        · simpa only [h, Function.update_self] using hCW i
        · simpa only [Function.update_of_ne h] using hW j)
    convert h using 1
    funext y
    congr 1
    ext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  have heq : (fun y => D.covariantTensorDerivative T y
      (Fin.cons (Y y) (fun i => W i y))) =ᶠ[𝓝 x]
      (fun y => mvfderiv (𝓡 n) f y (Y y) -
        ∑ i, T y (Function.update (fun j => W j y) i
          (D.covariantDerivativeOnFields Y (W i) y))) := by
    have hevent : ∀ᶠ y in 𝓝 x, ∀ i,
        MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (W i)) y :=
      Filter.eventually_all.mpr fun i => eventually_mdifferentiableAt_of_contMDiffAt (hW i)
    filter_upwards [hevent] with y hy
    exact D.covariantTensorDerivative_on_fields hT W y hy (Y y)
  have hderiv : mvfderiv (𝓡 n) (fun y => D.covariantTensorDerivative T y
      (Fin.cons (Y y) (fun i => W i y))) x =
      mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (Y y) -
        ∑ i, T y (Function.update (fun j => W j y) i
          (D.covariantDerivativeOnFields Y (W i) y))) x := by
    unfold mvfderiv
    rw [heq.mfderiv_eq]
    congr 2
  have hsub := mvfderiv_fun_sub
    ((contMDiffAt_mvfderiv_apply hTW hY).mdifferentiableAt (by simp))
    ((ContMDiffAt.sum (t := Finset.univ) fun i _ => hupdate i).mdifferentiableAt (by simp))
  have hfirst := D.covariantTensorDerivative_on_fields hT W x
    (fun i => (hW i).mdifferentiableAt (by simp))
    (D.covariantDerivativeOnFields X Y x)
  have hslot (i : Fin k) := D.covariantTensorDerivative_cons_update hT W
    (D.covariantDerivativeOnFields X (W i)) x
    (fun j => (hW j).mdifferentiableAt (by simp))
    ((D.contMDiffAt_covariantDerivativeOnFields hX (hW i)).mdifferentiableAt (by simp)) b i
  rw [covariantTensorDerivative]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ,
    Fin.update_cons_zero, ← Fin.cons_update]
  have hv (y : M) : (fun i : Fin (k + 1) => FiberBundle.extend (EuclideanSpace ℝ (Fin n))
      ((Fin.cons b v : Fin (k + 1) → TangentSpace (𝓡 n) x) i) y) =
      Fin.cons (Y y) (fun i => W i y) := by
    ext i
    cases i using Fin.cases <;> rfl
  simp_rw [hv]
  rw [hderiv, hsub]
  simp only [covariantDerivativeOnFields, X, Y, W, FiberBundle.extend_apply_self]
    at hfirst hslot ⊢
  rw [hfirst]
  simp_rw [hslot]
  simp only [sub_apply]
  ring



theorem covariantTensorDerivative_commutator
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (a b : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        (Fin.cons a (Fin.cons b v)) -
      D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        (Fin.cons b (Fin.cons a v)) =
      -∑ i, T x (Function.update v i (D.curvature x a b (v i))) := by
  classical
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  let W := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)
  let f := fun y => T y (fun i => W i y)
  have hX := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) a
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) b
  have hW (i : Fin k) :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) (v i)
  have hcomm := Poincare.Manifold.VectorField.mfderiv_mlieBracket_eq_commutator_of_contMDiffAt
    X Y x (hT.contMDiffAt_apply hW)
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
  have htors := D.covariantDerivativeOnFields_sub_swap
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
  have hexpand := secondCovariantTensorDerivative_expand D hT x a b v
  have hexpand' := secondCovariantTensorDerivative_expand D hT x b a v
  obtain ⟨A, hA⟩ := hT.1 x
  have hsum (p q : TangentSpace (𝓡 n) x) :
      mvfderiv (𝓡 n) (fun y => ∑ i, T y (Function.update (fun j => W j y) i
        (D.covariantDerivativeOnFields
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) p) (W i) y))) x q =
      ∑ i, mvfderiv (𝓡 n) (fun y => T y (Function.update (fun j => W j y) i
        (D.covariantDerivativeOnFields
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) p) (W i) y))) x q := by
    apply mvfderiv_sum_apply
    intro i
    have hU := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) p
    have hCW := D.contMDiffAt_covariantDerivativeOnFields hU (hW i)
    have h := hT.contMDiffAt_apply (x := x) (X := Function.update W i
      (D.covariantDerivativeOnFields (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) p) (W i)))
      (fun j => by
        by_cases h : j = i
        · simpa only [h, Function.update_self] using hCW
        · simpa only [Function.update_of_ne h] using hW j)
    convert h.mdifferentiableAt (by simp) using 1
    funext y
    congr 1
    ext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  let C := fun (p : TangentSpace (𝓡 n) x) (i : Fin k) => D.covariantDerivativeOnFields
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) p) (W i)
  have hdouble (p q : TangentSpace (𝓡 n) x) :
      (∑ i, ∑ j, T x (Function.update (Function.update v i (C p i x)) j
        (D.connection (Function.update W i (C p i) j) x q))) =
      ∑ i, ∑ j, A (Function.update (Function.update v i (C p i x)) j
        (if j = i then D.connection (C p i) x q else C q j x)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = i <;>
      simp [h, Function.update_of_ne, hA, C, covariantDerivativeOnFields]
  have hcancel := PoincareConjecture.slot_double_sum_sub A v
    (fun i => C a i x) (fun i => C b i x)
    (fun i => D.connection (C a i) x b) (fun i => D.connection (C b i) x a)
  have hcurv (i : Fin k) :
      T x (Function.update v i (D.connection (W i) x
          (D.covariantDerivativeOnFields X Y x))) -
        T x (Function.update v i (D.connection (W i) x
          (D.covariantDerivativeOnFields Y X x))) +
        A (Function.update v i (D.connection (C a i) x b - D.connection (C b i) x a)) =
      -T x (Function.update v i (D.curvature x a b (v i))) := by
    simp only [hA, A.map_update_sub, curvature, curvatureOnFields,
      FiberBundle.extend_apply_self]
    rw [← htors]
    simp only [map_sub, A.map_update_sub, C, covariantDerivativeOnFields,
      X, Y, W, FiberBundle.extend_apply_self]
    unfold covariantDerivativeOnFields
    ring
  dsimp only at hexpand hexpand'
  rw [hexpand, hexpand']
  rw [hsum b a, hsum a b]
  simp only [Finset.sum_sub_distrib]
  rw [hdouble a b, hdouble b a]
  have hcurv_sum := congrArg (fun z : Fin k → ℝ => ∑ i, z i) (funext hcurv)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib] at hcurv_sum
  rw [← htors, map_sub] at hcomm
  simp only [X, Y, FiberBundle.extend_apply_self] at hcomm
  linarith only [hcomm, hcancel, hcurv_sum]

end PoincareConjecture.LeviCivitaData
