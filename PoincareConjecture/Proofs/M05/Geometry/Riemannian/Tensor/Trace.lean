
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MetricTrace








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture


def bilinearOfTensorCons {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin (k + 2) => E) ℝ) (v : Fin k → E) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => A (Fin.cons a (Fin.cons b v)))
    (fun a a' b => by
      change A.curryLeft (a + a') (Fin.cons b v) = _
      simp only [map_add, add_apply, MultilinearMap.curryLeft_apply])
    (fun c a b => by
      change A.curryLeft (c • a) (Fin.cons b v) = _
      simp only [map_smul, smul_apply, MultilinearMap.curryLeft_apply])
    (fun a b b' => by
      change (A.curryLeft a).curryLeft (b + b') v = _
      simp only [map_add, add_apply, MultilinearMap.curryLeft_apply])
    (fun c a b => by
      change (A.curryLeft a).curryLeft (c • b) v = _
      simp only [map_smul, smul_apply, MultilinearMap.curryLeft_apply])

@[simp]
lemma bilinearOfTensorCons_apply {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin (k + 2) => E) ℝ) (v : Fin k → E)
    (a b : E) : bilinearOfTensorCons A v a b = A (Fin.cons a (Fin.cons b v)) := rfl

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

namespace RiemannianMetric


noncomputable def tensorTrace (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M (k + 2)) : CovariantTensorEvaluation n M k :=
  fun x v => ∑ i, T x (Fin.cons (g.orthonormalBasis x i)
    (Fin.cons (g.orthonormalBasis x i) v))

end RiemannianMetric

namespace LeviCivitaData



lemma covariantTensorDerivative_tensorTrace (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M (k + 2)} (hT : IsSmoothCovariantTensor T)
    (x : M) (u : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (g.tensorTrace T) x (Fin.cons u v) =
      ∑ i, D.covariantTensorDerivative T x
        (Fin.cons u (Fin.cons (g.orthonormalBasis x i)
          (Fin.cons (g.orthonormalBasis x i) v))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let X := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let V := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)
  let S : CovariantTensorEvaluation n M 2 :=
    fun y z => T y (Fin.cons (z 0) (Fin.cons (z 1) (fun i => V i y)))
  have hlin : ∀ᶠ y in nhds x, ∃ B : TangentSpace (𝓡 n) y →ₗ[ℝ]
      TangentSpace (𝓡 n) y →ₗ[ℝ] ℝ, ∀ a b, S y ![a, b] = B a b := by
    exact Filter.Eventually.of_forall fun y => by
      obtain ⟨A, hA⟩ := hT.1 y
      exact ⟨bilinearOfTensorCons A (fun i => V i y), fun a b => hA _⟩
  have hS (i j) : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun y => S y ![X i y, X j y]) x := by
    convert (hT.contMDiffAt_extend x (Fin.cons (b i) (Fin.cons (b j) v))).mdifferentiableAt
      (by simp) using 1
    ext y
    dsimp only [S, Fin.cons_zero, Fin.cons_succ]
    congr 1
    ext a
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;> rfl
  have htrace := mvfderiv_metricTrace_eq_fixed_trace_sub_gram (g := g) S x hlin hS u
  have hsum := mvfderiv_sum_apply (fun i y => S y ![X i y, X i y]) x u
    (fun i => hS i i)
  obtain ⟨A, hA⟩ := hT.1 x
  have hframe := bilinear_sum_frame_corrections (bilinearOfTensorCons A v) b
    (fun i => D.connection (X i) x u)
  have hgram (i j) :
      mvfderiv (𝓡 n) (fun y => g.inner y (X i y) (X j y)) x u =
        inner ℝ (D.connection (X i) x u) (b j) +
          inner ℝ (b i) (D.connection (X j) x u) :=
    D.mvfderiv_metric_extend x u (b i) (b j)
  simp only [bilinearOfTensorCons_apply, ← hA] at hframe
  change mvfderiv (𝓡 n) (fun y => ∑ i, S y ![g.orthonormalBasis y i,
      g.orthonormalBasis y i]) x u =
    mvfderiv (𝓡 n) (fun y => ∑ i, S y ![X i y, X i y]) x u -
      ∑ i, ∑ j, mvfderiv (𝓡 n) (fun y => g.inner y (X i y) (X j y)) x u *
        S x ![b i, b j] at htrace
  rw [hsum] at htrace
  simp only [hgram] at htrace
  have hSV (i j) : S x ![b i, b j] = T x (Fin.cons (b i) (Fin.cons (b j) v)) := by
    simp [S, V]
  simp only [hSV] at htrace
  rw [← hframe] at htrace
  simp only [covariantTensorDerivative, Fin.cons_succ, Fin.cons_zero,
    RiemannianMetric.tensorTrace]
  change mvfderiv (𝓡 n) (fun y => ∑ i, S y ![g.orthonormalBasis y i,
      g.orthonormalBasis y i]) x u -
    ∑ j, ∑ i, T x (Fin.cons (b i) (Fin.cons (b i)
      (Function.update v j (D.connection (V j) x u)))) = _
  rw [htrace]
  have hext (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) (y : M) :
      (fun j : Fin (k + 2) => FiberBundle.extend
      (E := (TangentSpace (𝓡 n) : M → Type _)) (EuclideanSpace ℝ (Fin n))
      ((Fin.cons (b i) (Fin.cons (b i) v) : Fin (k + 2) → TangentSpace (𝓡 n) x) j) y) =
      Fin.cons (X i y) (Fin.cons (X i y) (fun j => V j y)) := by
    funext j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> rfl
  simp only [← Finset.sum_sub_distrib]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.update_cons_zero, ← Fin.cons_update]
  simp_rw [show g.orthonormalBasis x = b from rfl, hext]
  rw [Finset.sum_comm (f := fun j i => T x
    (Fin.cons (b i) (Fin.cons (b i) (Function.update v j (D.connection (V j) x u)))))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [S, X, V, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring


lemma covariantTensorDerivative_tensorLaplacian (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (u : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.tensorLaplacian T) x (Fin.cons u v) =
      ∑ i, D.iteratedCovariantTensorDerivative T 3 x
        (Fin.cons u (Fin.cons (g.orthonormalBasis x i)
          (Fin.cons (g.orthonormalBasis x i) v))) := by
  exact D.covariantTensorDerivative_tensorTrace
    (hD.2.2.1 _ _ (hD.2.2.1 _ _ hT)) x u v

end LeviCivitaData

end PoincareConjecture
