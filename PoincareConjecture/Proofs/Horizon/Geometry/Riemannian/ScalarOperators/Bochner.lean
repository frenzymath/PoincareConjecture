import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Derivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Commutation










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma contMDiffAt_inner_fields
    {V W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => g.inner y (V y) (W y)) x := by
  have h := ((g.contMDiff x).clm_bundle_apply hV).clm_bundle_apply hW
  simpa using (contMDiffAt_totalSpace.mp h).2


theorem mvfderiv_normSq (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hV : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% V) x)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => g.inner y (V y) (V y)) x v =
      2 * g.inner x (D.connection V x v) (V x) := by
  have h := D.horizon_mvfderiv_inner (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) hV hV
  simp only [covariantDerivativeOnFields, FiberBundle.extend_apply_self] at h
  rw [g.symm x (V x)] at h
  linarith


theorem hessianOnFields_normSq (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    (X Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    D.hessianOnFields (fun y => g.inner y (V y) (V y)) X Y x =
      2 * g.inner x
        (D.connection (D.covariantDerivativeOnFields Y V) x (X x) -
          D.connection V x (D.connection Y x (X x))) (V x) +
      2 * g.inner x (D.connection V x (Y x)) (D.connection V x (X x)) := by
  have hW := D.contMDiffAt_covariantDerivativeOnFields hY (hV x)
  have hi := (contMDiffAt_inner_fields (g := g) hW (hV x)).mdifferentiableAt (by simp)
  have hderiv := D.horizon_mvfderiv_inner X (hW.mdifferentiableAt (by simp))
    ((hV x).mdifferentiableAt (by simp))
  have hnorm (y : M) (v : TangentSpace (𝓡 n) y) :=
    D.mvfderiv_normSq ((hV y).mdifferentiableAt (by simp)) v
  unfold hessianOnFields
  simp_rw [hnorm]
  dsimp only [covariantDerivativeOnFields] at hi
  rw [mvfderiv_fun_mul (f := fun _ : M => (2 : ℝ)) mdifferentiableAt_const hi]
  simp only [mvfderiv_const, smul_zero, add_zero, smul_apply,
    smul_eq_mul]
  change 2 * mvfderiv (𝓡 n)
    (fun y => g.inner y (D.covariantDerivativeOnFields Y V y) (V y)) x (X x) -
      2 * g.inner x (D.connection V x (D.connection Y x (X x))) (V x) = _
  rw [hderiv]
  simp only [covariantDerivativeOnFields, map_sub, sub_apply]
  ring


theorem hessian_normSq (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => g.inner y (V y) (V y)) x u v =
      2 * g.inner x
        (D.connection (D.covariantDerivativeOnFields
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) V) x u -
          D.connection V x
            (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x u)) (V x) +
      2 * g.inner x (D.connection V x v) (D.connection V x u) := by
  unfold hessian
  rw [D.hessianOnFields_normSq hV _ _
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)]
  simp only [FiberBundle.extend_apply_self]


theorem laplacian_normSq (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    (x : M) :
    let b := g.orthonormalBasis x
    let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    D.laplacian (fun y => g.inner y (V y) (V y)) x =
      2 * ∑ i, g.inner x
        (D.connection (D.covariantDerivativeOnFields (E i) V) x (b i) -
          D.connection V x (D.connection (E i) x (b i))) (V x) +
      2 * ∑ i, g.inner x (D.connection V x (b i)) (D.connection V x (b i)) := by
  dsimp only
  unfold laplacian
  simp_rw [D.hessian_normSq hV]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]


theorem sum_hessian_sq_eq_inner_connection_gradient (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (v : TangentSpace (𝓡 n) x) :
    (∑ j, (D.hessian f x v (g.orthonormalBasis x j)) ^ 2) =
      g.inner x (D.connection (D.gradient f) x v) (D.connection (D.gradient f) x v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp_rw [D.hessian_eq_inner_connection_gradient hf]
  have h := (g.orthonormalBasis x).sum_inner_mul_inner
    (D.connection (D.gradient f) x v) (D.connection (D.gradient f) x v)
  convert h using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro j _
  change (inner ℝ (D.connection (D.gradient f) x v) (g.orthonormalBasis x j)) ^ 2 = _
  rw [real_inner_comm (g.orthonormalBasis x j), pow_two]


theorem laplacian_gradient_normSq (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    let b := g.orthonormalBasis x
    let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    D.laplacian (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x =
      2 * ∑ i, g.inner x
        (D.connection (D.covariantDerivativeOnFields (E i) (D.gradient f)) x (b i) -
          D.connection (D.gradient f) x (D.connection (E i) x (b i))) (D.gradient f x) +
      2 * ∑ i, ∑ j, (D.hessian f x (b i) (b j)) ^ 2 := by
  dsimp only
  rw [D.laplacian_normSq (D.contMDiff_gradient hf)]
  simp_rw [D.sum_hessian_sq_eq_inner_connection_gradient (hf x)]


theorem laplacian_gradient_normSq_eq_third_derivative (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    D.laplacian (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x =
      2 * (∑ i, D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x
        ![g.orthonormalBasis x i, g.orthonormalBasis x i, D.gradient f x]) +
      2 * ∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2 := by
  rw [D.laplacian_gradient_normSq hf]
  simp_rw [D.covariantTensorDerivative_hessian_eq hf]


theorem sum_covariantTensorDerivative_hessian_gradient (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (∑ i, D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i, D.gradient f x]) =
      mvfderiv (𝓡 n) (D.laplacian f) x (D.gradient f x) +
        D.ricci x (D.gradient f x) (D.gradient f x) := by
  have hswap (a b c : TangentSpace (𝓡 n) x) :
      D.curvature x a b c = -D.curvature x b a c := by
    unfold curvature curvatureOnFields
    have hbr := congrArg (fun F => F x) (VectorField.mlieBracket_swap (I := 𝓡 n)
      (V := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b)
      (W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a))
    simp only [Pi.neg_apply] at hbr
    rw [hbr]
    simp only [map_neg]
    module
  have hterm (i) :
      D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x
        ![g.orthonormalBasis x i, g.orthonormalBasis x i, D.gradient f x] =
      D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x
        ![D.gradient f x, g.orthonormalBasis x i, g.orthonormalBasis x i] +
      D.curvatureTensor x (D.gradient f x) (g.orthonormalBasis x i)
        (D.gradient f x) (g.orthonormalBasis x i) := by
    rw [D.covariantTensorDerivative_hessian_symm hf]
    have h := D.covariantTensorDerivative_hessian_commutator hf x
      (g.orthonormalBasis x i) (D.gradient f x) (g.orthonormalBasis x i)
    rw [hswap, map_neg, neg_neg, ← D.inner_gradient, g.symm] at h
    simpa only [curvatureTensor, add_comm] using (sub_eq_iff_eq_add).mp h
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, D.sum_covariantTensorDerivative_hessian_eq hf]
  rfl



theorem bochner_identity (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    D.laplacian (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x =
      2 * (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) +
      2 * mvfderiv (𝓡 n) (D.laplacian f) x (D.gradient f x) +
      2 * D.ricci x (D.gradient f x) (D.gradient f x) := by
  rw [D.laplacian_gradient_normSq_eq_third_derivative hf,
    D.sum_covariantTensorDerivative_hessian_gradient hf]
  ring

end PoincareConjecture.LeviCivitaData
