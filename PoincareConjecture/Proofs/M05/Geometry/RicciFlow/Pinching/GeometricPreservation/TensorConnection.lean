import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.Connection
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.DerivativeRegularity

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

def transportPullbackTensor (F : RicciFlow n M (Ico a b)) (t : ℝ)
    {k : ℕ} (T : CovariantTensorEvaluation n M k) : CovariantTensorEvaluation n M k :=
  fun x v => T x (fun i => canonicalTransport F t x (v i))

def transportedTensorDerivative (F : RicciFlow n M (Ico a b)) {t : ℝ}
    (ht : t ∈ Ico a b) {k : ℕ} (T : CovariantTensorEvaluation n M k) :
    CovariantTensorEvaluation n M (k + 1) :=
  fun x v =>
    mvfderiv (𝓡 n)
      (fun y => T y (fun i =>
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) x (v 0) -
      ∑ i, T x (Function.update (fun j => v j.succ) i
        (transportedConnection F ht
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ)) x (v 0)))

theorem transportPullbackTensor_isSmooth
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (transportPullbackTensor F t T) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 x
    exact ⟨A.compLinearMap (fun _ => (canonicalTransport F t x).toLinearMap),
      fun v => hA _⟩
  · intro O hO Y hY
    apply hT.2 O hO (fun i y => canonicalTransport F t y (Y i y))
    intro i
    exact (canonicalTransport_contMDiff_space F ht).contMDiffOn.clm_bundle_apply (hY i)

theorem transportedTensorDerivative_pullback
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (u : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    transportedTensorDerivative F ht (transportPullbackTensor F t T) x (Fin.cons u v) =
      (F.connection t).covariantTensorDerivative T x
        (Fin.cons u (fun i => canonicalTransport F t x (v i))) := by
  let Y := fun i y => canonicalTransport F t y
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)
  have hY (i : Fin k) : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (Y i)) x :=
    ((canonicalTransport_contMDiff_space F ht x).mdifferentiableAt (by simp)).clm_bundle_apply
      (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (v i))
  have h := (F.connection t).covariantTensorDerivative_on_fields hT Y x hY u
  simp only [Y, FiberBundle.extend_apply_self] at h
  rw [h]
  simp only [transportedTensorDerivative, transportPullbackTensor,
    Fin.cons_zero, Fin.cons_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, transportedConnection_apply]
    rw [← orthonormalTransport_toContinuousLinearMap F t x]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  · simp only [Function.update_of_ne hji]

theorem transportedTensorDerivative_on_fields
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (Y : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hY : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (Y i)) x)
    (u : TangentSpace (𝓡 n) x) :
    transportedTensorDerivative F ht (transportPullbackTensor F t T) x
        (Fin.cons u (fun i => Y i x)) =
      mvfderiv (𝓡 n) (fun y => transportPullbackTensor F t T y (fun i => Y i y)) x u -
        ∑ i, transportPullbackTensor F t T x
          (Function.update (fun j => Y j x) i (transportedConnection F ht (Y i) x u)) := by
  rw [transportedTensorDerivative_pullback F ht hT]
  rw [(F.connection t).covariantTensorDerivative_on_fields hT
    (fun i y => canonicalTransport F t y (Y i y)) x
    (fun i => ((canonicalTransport_contMDiff_space F ht x).mdifferentiableAt
      (by simp)).clm_bundle_apply (hY i)) u]
  unfold transportPullbackTensor
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, transportedConnection_apply]
    rw [← orthonormalTransport_toContinuousLinearMap F t x]
    exact (ContinuousLinearEquiv.apply_symm_apply _ _).symm
  · simp only [Function.update_of_ne hji]

def mixedTensorDerivative (F : RicciFlow n M (Ico a b)) {t : ℝ}
    (ht : t ∈ Ico a b) {k : ℕ} (S : CovariantTensorEvaluation n M (k + 1)) :
    CovariantTensorEvaluation n M (k + 2) :=
  fun x v =>
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v 1)
    let Y := fun i : Fin k => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ.succ)
    mvfderiv (𝓡 n) (fun y => S y (Fin.cons (X y) (fun i => Y i y))) x (v 0) -
      S x (Fin.cons ((F.connection t).connection X x (v 0)) (fun i => v i.succ.succ)) -
      ∑ i, S x (Fin.cons (v 1) (Function.update (fun j => v j.succ.succ) i
        (transportedConnection F ht (Y i) x (v 0))))

theorem mixedTensorDerivative_pullback
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (u w : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    mixedTensorDerivative F ht
        (transportedTensorDerivative F ht (transportPullbackTensor F t T)) x
        (Fin.cons u (Fin.cons w v)) =
      (F.connection t).covariantTensorDerivative
        ((F.connection t).covariantTensorDerivative T) x
        (Fin.cons u (Fin.cons w (fun i => canonicalTransport F t x (v i)))) := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  let Y := fun i y => canonicalTransport F t y
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)
  let Y' : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y :=
    fun i => Fin.cases X (fun j => Y j) i
  have hY (i : Fin k) : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (Y i)) x :=
    ((canonicalTransport_contMDiff_space F ht x).mdifferentiableAt (by simp)).clm_bundle_apply
      (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (v i))
  have hfields (i : Fin (k + 1)) : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (Y' i)) x := by
    cases i using Fin.cases with
    | zero => exact FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
    | succ i => exact hY i
  have h := (F.connection t).covariantTensorDerivative_on_fields
    ((F.connection t).covariantTensorDerivative_isSmooth hT) Y' x hfields u
  have hcons (y : M) : (fun i => Y' i y) =
      Fin.cons (X y) (fun i => Y i y) := by
    ext i
    cases i using Fin.cases <;> rfl
  simp only [hcons, X, Y, FiberBundle.extend_apply_self] at h
  rw [h]
  simp only [mixedTensorDerivative, Fin.cons_zero, Fin.cons_succ,
    transportedTensorDerivative_pullback F ht hT, Fin.sum_univ_succ,
    Fin.update_cons_zero, ← Fin.cons_update]
  rw [sub_add_eq_sub_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, transportedConnection_apply]
    rw [← orthonormalTransport_toContinuousLinearMap F t x]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  · simp only [Function.update_of_ne hji]

def transportedTensorLaplacian (F : RicciFlow n M (Ico a b)) {t : ℝ}
    (ht : t ∈ Ico a b) {k : ℕ} (T : CovariantTensorEvaluation n M k) :
    CovariantTensorEvaluation n M k :=
  fun x v => ∑ i, mixedTensorDerivative F ht (transportedTensorDerivative F ht T) x
    (Fin.cons ((F.metric t).orthonormalBasis x i)
      (Fin.cons ((F.metric t).orthonormalBasis x i) v))

theorem transportedTensorLaplacian_pullback
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) :
    transportedTensorLaplacian F ht (transportPullbackTensor F t T) =
      transportPullbackTensor F t ((F.connection t).tensorLaplacian T) := by
  funext x v
  simp only [transportedTensorLaplacian, transportPullbackTensor,
    LeviCivitaData.tensorLaplacian, LeviCivitaData.iteratedCovariantTensorDerivative]
  apply Finset.sum_congr rfl
  intro i _
  exact mixedTensorDerivative_pullback F ht hT x _ _ v

theorem canonicalTransport_curvature_pde_on_initial_tensor
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Ico a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt
      (fun s => (F.connection s).curvatureTensor x
        (canonicalTransport F s x u) (canonicalTransport F s x v)
        (canonicalTransport F s x w) (canonicalTransport F s x z))
      (transportedTensorLaplacian F ⟨ht.1.le, ht.2⟩
          (transportPullbackTensor F t (F.connection t).riemannEvaluation) x
          ![u, v, w, z] +
        2 * ((F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x v)
            (canonicalTransport F t x w) (canonicalTransport F t x z) -
      (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x v)
            (canonicalTransport F t x z) (canonicalTransport F t x w) -
          (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x z)
            (canonicalTransport F t x v) (canonicalTransport F t x w) +
          (F.connection t).curvatureB x
            (canonicalTransport F t x u) (canonicalTransport F t x w)
            (canonicalTransport F t x v) (canonicalTransport F t x z))) t := by
  have hsmooth : IsSmoothCovariantTensor (F.connection t).riemannEvaluation :=
    (hC.tensor_calculus n M (F.metric t) (F.connection t)).1
  have h := canonicalTransport_hasDerivAt_curvature hC F ht x u v w z
  have hl := congrFun (transportedTensorLaplacian_pullback F ⟨ht.1.le, ht.2⟩ hsmooth) x
  have hl' := congrFun hl ![u, v, w, z]
  simp only [transportPullbackTensor] at hl'
  have htuple : (fun i => canonicalTransport F t x (![u, v, w, z] i)) =
      ![canonicalTransport F t x u, canonicalTransport F t x v,
        canonicalTransport F t x w, canonicalTransport F t x z] := by
    ext i
    fin_cases i <;> rfl
  have hl'' : transportedTensorLaplacian F ⟨ht.1.le, ht.2⟩
      (transportPullbackTensor F t (F.connection t).riemannEvaluation) x ![u, v, w, z] =
      (F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
        ![canonicalTransport F t x u, canonicalTransport F t x v,
          canonicalTransport F t x w, canonicalTransport F t x z] := by
    rw [hl', htuple]
  rw [← hl''] at h
  exact h

end PoincareConjecture.RicciFlow.Frame
