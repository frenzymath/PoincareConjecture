import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.GradientCommutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.ProductDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MetricDuality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.DerivativeRegularity









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


def tensorDivergence (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M (k + 1)) : CovariantTensorEvaluation n M k :=
  g.tensorTrace (D.covariantTensorDerivative T)

private def swapFirstTwo : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective ![1, 0, 2] (by decide)


def twoTensorCodazziDefect (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 2) : CovariantTensorEvaluation n M 3 :=
  fun x v => D.covariantTensorDerivative T x v -
    D.covariantTensorDerivative T x (v ∘ swapFirstTwo)


def twoTensorCurvatureTrace (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 2) : CovariantTensorEvaluation n M 2 :=
  fun x v => -(∑ k, (
    T x ![D.curvature x (g.orthonormalBasis x k) (v 0)
      (g.orthonormalBasis x k), v 1] +
    T x ![g.orthonormalBasis x k,
      D.curvature x (g.orthonormalBasis x k) (v 0) (v 1)]))


def twoTensorDivergenceFlux (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 2) : CovariantTensorEvaluation n M 3 :=
  fun x v => g.inner x (v 0) (v 1) * D.tensorDivergence T x ![v 2] +
    D.twoTensorCodazziDefect T x v


def hessianCurvatureFlux (D : LeviCivitaData g) (f : M → ℝ) :
    CovariantTensorEvaluation n M 3 :=
  fun x v => g.inner x (v 0) (v 1) * D.ricci x (D.gradient f x) (v 2) -
    mvfderiv (𝓡 n) f x (D.curvature x (v 0) (v 1) (v 2))

private lemma twoTensorCodazziDefect_isSmooth (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.twoTensorCodazziDefect T) := by
  have hS := D.covariantTensorDerivative_isSmooth hT
  exact hS.sub (hS.perm swapFirstTwo)

private lemma covariantTensorDerivative_twoTensorCodazziDefect
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 2}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (d a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.twoTensorCodazziDefect T) x ![d, a, b, c] =
      D.covariantTensorDerivative (D.covariantTensorDerivative T) x ![d, a, b, c] -
        D.covariantTensorDerivative (D.covariantTensorDerivative T) x ![d, b, a, c] := by
  have hS := D.covariantTensorDerivative_isSmooth hT
  unfold twoTensorCodazziDefect
  rw [D.covariantTensorDerivative_sub hS (hS.perm swapFirstTwo)]
  dsimp only
  rw [D.covariantTensorDerivative_reindex]
  congr 2
  ext i
  fin_cases i <;> rfl



theorem tensorLaplacian_eq_divergence_codazzi (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian T x ![a, b] =
      D.covariantTensorDerivative (D.tensorDivergence T) x ![a, b] +
        D.tensorDivergence (D.twoTensorCodazziDefect T) x ![a, b] +
        D.twoTensorCurvatureTrace T x ![a, b] := by
  have hS := D.covariantTensorDerivative_isSmooth hT
  have htrace := D.covariantTensorDerivative_tensorTrace hS x a ![b]
  change D.covariantTensorDerivative (D.tensorDivergence T) x ![a, b] =
    ∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative T) x
      ![a, g.orthonormalBasis x i, g.orthonormalBasis x i, b] at htrace
  rw [htrace]
  change (∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative T) x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i, a, b]) =
    (∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative T) x
      ![a, g.orthonormalBasis x i, g.orthonormalBasis x i, b]) +
    (∑ i, D.covariantTensorDerivative (D.twoTensorCodazziDefect T) x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i, a, b]) -
    (∑ i, (T x ![D.curvature x (g.orthonormalBasis x i) a
      (g.orthonormalBasis x i), b] +
      T x ![g.orthonormalBasis x i, D.curvature x (g.orthonormalBasis x i) a b]))
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.covariantTensorDerivative_twoTensorCodazziDefect hT]
  have hc := D.covariantTensorDerivative_commutator_two hT x
    (g.orthonormalBasis x i) a (g.orthonormalBasis x i) b
  linarith

private lemma metric_isSmoothCovariantTensor :
    IsSmoothCovariantTensor (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
      g.inner x (v 0) (v 1)) := by
  constructor
  · intro x
    let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 n) x) ℝ :=
      { toFun := fun v => g.inner x (v 0) (v 1)
        map_update_add' := by
          intro _ v i a b
          fin_cases i <;> simp [map_add]
        map_update_smul' := by
          intro _ v i c a
          fin_cases i <;> simp }
    exact ⟨A, fun _ => rfl⟩
  · intro U hU X hX
    have hi := (g.contMDiff.contMDiffOn.clm_bundle_apply (hX 0)).clm_bundle_apply (hX 1)
    intro x hx
    have hs := (Bundle.contMDiffAt_totalSpace.mp
      ((hi x hx).contMDiffAt (hU.mem_nhds hx))).2
    exact hs.contMDiffWithinAt

private lemma metric_oneTensor_product_eq
    (β : CovariantTensorEvaluation n M 1) :
    tensorProduct (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
      g.inner x (v 0) (v 1)) β =
      (fun x v => g.inner x (v 0) (v 1) * β x ![v 2]) := by
  funext x v
  unfold tensorProduct
  congr 1
  congr 1
  ext i
  fin_cases i
  rfl

private lemma tensorDivergence_metric_oneTensor (D : LeviCivitaData g)
    {β : CovariantTensorEvaluation n M 1} (hβ : IsSmoothCovariantTensor β)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    D.tensorDivergence (fun y v => g.inner y (v 0) (v 1) * β y ![v 2]) x ![a, b] =
      D.covariantTensorDerivative β x ![a, b] := by
  have hprod (u c d z : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative
          (fun y v => g.inner y (v 0) (v 1) * β y ![v 2]) x ![u, c, d, z] =
        g.inner x c d * D.covariantTensorDerivative β x ![u, z] := by
    rw [← metric_oneTensor_product_eq β]
    have hp := D.covariantTensorDerivative_tensorProduct
      (metric_isSmoothCovariantTensor (g := g)) hβ x u ![c, d, z]
    have hc : (fun i : Fin 2 => ![c, d, z] (Fin.castAdd 1 i)) = ![c, d] := by
      ext i
      fin_cases i <;> rfl
    have hz : (fun i : Fin 1 => ![c, d, z] (Fin.natAdd 2 i)) = ![z] := by
      ext i
      fin_cases i
      rfl
    rw [hc, hz] at hp
    simpa only [Matrix.Fin.cons_vecCons, D.covariantTensorDerivative_metric_eq_zero,
      zero_mul, zero_add, Matrix.cons_val_zero, Matrix.cons_val_one] using hp
  change (∑ i, D.covariantTensorDerivative
      (fun y v => g.inner y (v 0) (v 1) * β y ![v 2]) x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i, a, b]) = _
  simp_rw [hprod]
  have hlin := (D.covariantTensorDerivative_isSmooth hβ).update_eq_sum g x ![a, b] 0 a
  have hup (z : TangentSpace (𝓡 n) x) : Function.update ![a, b] 0 z = ![z, b] := by
    ext i
    fin_cases i <;> simp
  simp only [hup] at hlin
  simpa only [g.symm x a] using hlin.symm


theorem tensorLaplacian_eq_divergence_flux (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian T x ![a, b] =
      D.tensorDivergence (D.twoTensorDivergenceFlux T) x ![a, b] +
        D.twoTensorCurvatureTrace T x ![a, b] := by
  have hβ : IsSmoothCovariantTensor (D.tensorDivergence T) :=
    (D.covariantTensorDerivative_isSmooth hT).tensorTrace
  have hprod : IsSmoothCovariantTensor (k := 3)
      (fun y v => g.inner y (v 0) (v 1) * D.tensorDivergence T y ![v 2]) := by
    rw [← metric_oneTensor_product_eq]
    exact isSmoothCovariantTensor_tensorProduct metric_isSmoothCovariantTensor hβ
  have hsplit : D.tensorDivergence (D.twoTensorDivergenceFlux T) x ![a, b] =
      D.tensorDivergence
        (fun y v => g.inner y (v 0) (v 1) * D.tensorDivergence T y ![v 2]) x ![a, b] +
        D.tensorDivergence (D.twoTensorCodazziDefect T) x ![a, b] := by
    unfold tensorDivergence twoTensorDivergenceFlux
    rw [D.covariantTensorDerivative_add hprod (D.twoTensorCodazziDefect_isSmooth hT)]
    simp only [RiemannianMetric.tensorTrace, Finset.sum_add_distrib]
    rfl
  rw [hsplit, D.tensorDivergence_metric_oneTensor hβ]
  exact D.tensorLaplacian_eq_divergence_codazzi hT x a b

private lemma covariantTensorDerivative_eq_of_eventuallyEq
    (D : LeviCivitaData g) {k : ℕ} {S T : CovariantTensorEvaluation n M k}
    {x : M} (h : ∀ᶠ y in 𝓝 x, ∀ v, S y v = T y v)
    (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative S x v = D.covariantTensorDerivative T x v := by
  have hx := h.self_of_nhds
  have he : (fun y => S y (fun i =>
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) =ᶠ[𝓝 x]
      (fun y => T y (fun i =>
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) :=
    h.mono fun y hy => hy _
  simp only [covariantTensorDerivative, Poincare.mvfderiv_eq_of_eventuallyEq he, hx]



theorem twoTensorDivergenceFlux_hessian_eventuallyEq (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (hharm : D.laplacian f =ᶠ[𝓝 x] fun _ => 0) :
    ∀ᶠ y in 𝓝 x, ∀ v,
      D.twoTensorDivergenceFlux (fun z w => D.hessian f z (w 0) (w 1)) y v =
        D.hessianCurvatureFlux f y v := by
  filter_upwards [hharm.eventuallyEq_nhds] with y hy
  intro v
  have hdiv := D.sum_covariantTensorDerivative_hessian_apply hf y (v 2)
  rw [Poincare.mvfderiv_eq_of_eventuallyEq hy, mvfderiv_const, zero_apply,
    zero_add] at hdiv
  change D.tensorDivergence (fun z w => D.hessian f z (w 0) (w 1)) y ![v 2] =
    D.ricci y (D.gradient f y) (v 2) at hdiv
  have hc := D.covariantTensorDerivative_hessian_commutator hf y (v 0) (v 1) (v 2)
  have hv : v = ![v 0, v 1, v 2] := by
    ext i
    fin_cases i <;> rfl
  have hperm : v ∘ swapFirstTwo = ![v 1, v 0, v 2] := by
    ext i
    fin_cases i <;> rfl
  unfold twoTensorDivergenceFlux twoTensorCodazziDefect hessianCurvatureFlux
  rw [hdiv, hperm]
  have hc' : D.covariantTensorDerivative (fun z w => D.hessian f z (w 0) (w 1)) y v -
      D.covariantTensorDerivative (fun z w => D.hessian f z (w 0) (w 1)) y
        ![v 1, v 0, v 2] =
      -mvfderiv (𝓡 n) f y (D.curvature y (v 0) (v 1) (v 2)) := by
    conv_lhs => lhs; rw [hv]
    exact hc
  rw [hc']
  ring



theorem tensorLaplacian_hessian_eq_divergence_curvature (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (hharm : D.laplacian f =ᶠ[𝓝 x] fun _ => 0)
    (a b : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y v => D.hessian f y (v 0) (v 1)) x ![a, b] =
      D.tensorDivergence (D.hessianCurvatureFlux f) x ![a, b] +
        D.twoTensorCurvatureTrace (fun y v => D.hessian f y (v 0) (v 1)) x ![a, b] := by
  rw [D.tensorLaplacian_eq_divergence_flux (D.hessian_isSmoothCovariantTensor hf)]
  congr 1
  unfold tensorDivergence RiemannianMetric.tensorTrace
  apply Finset.sum_congr rfl
  intro i _
  exact D.covariantTensorDerivative_eq_of_eventuallyEq
    (D.twoTensorDivergenceFlux_hessian_eventuallyEq hf x hharm) _

end PoincareConjecture.LeviCivitaData
