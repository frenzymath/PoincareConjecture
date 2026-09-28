import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Manifold.PartitionOfUnity.Derivative









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle VectorField
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}


theorem covariantTensorDerivative_eq_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {x : M}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {k : ℕ} {S : CovariantTensorEvaluation n M k} {T : CovariantTensorEvaluation n N k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hST : ∀ᶠ y in 𝓝 x, ∀ v,
      S y v = T (f y) (fun i => mfderiv (𝓡 n) (𝓡 n) f y (v i)))
    (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative S x v =
      D'.covariantTensorDerivative T (f x)
        (fun i => mfderiv (𝓡 n) (𝓡 n) f x (v i)) := by
  classical
  let A := mfderiv (𝓡 n) (𝓡 n) f x
  let Y := fun i : Fin k => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (A (v i.succ))
  let P := fun i => mpullback (𝓡 n) (𝓡 n) f (Y i)
  have hY (i : Fin k) : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (Y i)) (f x) := FiberBundle.contMDiffAt_extend _ _ _
  have hP (i : Fin k) : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (P i)) x :=
    (hY i).mpullback_vectorField_preimage hf hinv.self_of_nhds (by simp)
  have hPx (i : Fin k) : P i x = v i.succ := by
    simp only [P, Y, A, mpullback_apply, FiberBundle.extend_apply_self,
      hinv.self_of_nhds.inverse_apply_self]
  have hYx (i : Fin k) : Y i (f x) = A (v i.succ) :=
    FiberBundle.extend_apply_self _ _
  have heval : (fun y => S y (fun i => P i y)) =ᶠ[𝓝 x]
      (fun y => T (f y) (fun i => Y i (f y))) := by
    filter_upwards [hST, hinv] with y hy hi
    rw [hy]
    simp only [P, mpullback_apply, hi.self_apply_inverse]
  have hleft := D.covariantTensorDerivative_on_fields hS P x
    (fun i => (hP i).mdifferentiableAt (by simp)) (v 0)
  have hright := D'.covariantTensorDerivative_on_fields hT Y (f x)
    (fun i => (hY i).mdifferentiableAt (by simp)) (A (v 0))
  have hchain := mvfderiv_comp x
    ((hT.contMDiffAt_apply hY).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  have hd : mvfderiv (𝓡 n) (fun y => S y (fun i => P i y)) x (v 0) =
      mvfderiv (𝓡 n) (fun y => T y (fun i => Y i y)) (f x) (A (v 0)) := by
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heval]
    exact congrArg (fun L => L (v 0)) hchain
  have hslot (i : Fin k) :
      S x (Function.update (fun j => P j x) i (D.connection (P i) x (v 0))) =
      T (f x) (Function.update (fun j => Y j (f x)) i
        (D'.connection (Y i) (f x) (A (v 0)))) := by
    rw [hST.self_of_nhds, D.connection_mpullback_of_metric_pullback D' hf hinv hmetric
      ((hY i).mdifferentiableAt (by simp))]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, hinv.self_of_nhds.self_apply_inverse]
      rfl
    · simp only [Function.update_of_ne hj, P, mpullback_apply,
        hinv.self_of_nhds.self_apply_inverse]
  rw [hd] at hleft
  simp_rw [hslot] at hleft
  have hsource : Fin.cons (v 0) (fun i => P i x) = v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact hPx j
  have htarget : Fin.cons (A (v 0)) (fun i => Y i (f x)) = fun i => A (v i) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact hYx j
  rw [hsource] at hleft
  rw [htarget] at hright
  exact hleft.trans hright.symm


theorem iteratedCovariantTensorDerivative_eq_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {k : ℕ} {S : CovariantTensorEvaluation n M k} {T : CovariantTensorEvaluation n N k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hST : ∀ y ∈ U, ∀ v,
      S y v = T (f y) (fun i => mfderiv (𝓡 n) (𝓡 n) f y (v i)))
    (m : ℕ) {x : M} (hx : x ∈ U) (v : Fin (k + m) → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative S m x v =
      D'.iteratedCovariantTensorDerivative T m (f x)
        (fun i => mfderiv (𝓡 n) (𝓡 n) f x (v i)) := by
  induction m generalizing x with
  | zero => exact hST x hx v
  | succ m ih =>
      apply D.covariantTensorDerivative_eq_pullback D'
        (hf.contMDiffAt (hU.mem_nhds hx))
        (Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hinv y hy))
        (Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hmetric y hy))
        (D.iteratedCovariantTensorDerivative_isSmooth hS m)
        (D'.iteratedCovariantTensorDerivative_isSmooth hT m)
      exact Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih hy)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]


theorem tensorNorm_eq_of_linearEquiv
    (g : RiemannianMetric n M) (h : RiemannianMetric n N) {k : ℕ}
    (S : CovariantTensorEvaluation n M k) (T : CovariantTensorEvaluation n N k)
    (x : M) (y : N) (e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) y)
    (hmetric : ∀ u v, h.inner y (e u) (e v) = g.inner x u v)
    (hST : ∀ v, S x v = T y (fun i => e (v i)))
    (A : MultilinearMap ℝ (fun _ : Fin k => TangentSpace (𝓡 n) y) ℝ)
    (hA : ∀ v, T y v = A v) : g.tensorNorm S x = h.tensorNorm T y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner hmetric
  have hc := multilinear_sum_sq_comp_linearIsometryEquiv A e'
    (g.orthonormalBasis x) (h.orthonormalBasis y)
  unfold tensorNorm
  apply congrArg Real.sqrt
  simp_rw [hST, hA]
  exact hc

end PoincareConjecture.RiemannianMetric
