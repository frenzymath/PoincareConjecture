import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.MetricDuality
import PoincareConjecture.Definitions.Ch01.ScalarOperators

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Bundle

namespace PoincareConjecture

universe u

namespace LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def gradient (D : LeviCivitaData g) (f : M → ℝ) (x : M) :
    TangentSpace (𝓡 n) x :=
  (g.inner x).inverse (mvfderiv (𝓡 n) f x)

theorem inner_gradient (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    g.inner x (D.gradient f x) v = mvfderiv (𝓡 n) f x v := by
  have hi : mvfderiv (𝓡 n) f x = g.inner x (D.gradient f x) :=
    (g.inner_isInvertible x).inverse_apply_eq.mp
      (rfl : (g.inner x).inverse (mvfderiv (𝓡 n) f x) = D.gradient f x)
  exact (congrArg (fun q ↦ q v) hi).symm

theorem contMDiffAt_gradient (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.gradient f)) x := by
  apply g.contMDiffAt_of_metricDual
  have heq (y : M) : g.inner y (D.gradient f y) = mvfderiv (𝓡 n) f y := by
    ext v
    exact D.inner_gradient f y v
  simp_rw [heq]
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  convert hf.mfderiv_const (m := ∞) (by simp) using 1
  funext y
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv,
    NormedSpace.fromTangentSpace]
  rfl

theorem contMDiff_gradient (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.gradient f)) :=
  fun x => D.contMDiffAt_gradient (hf x)

theorem hessianOnFields_eq_inner_connection_gradient (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (X : (y : M) → TangentSpace (𝓡 n) y)
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) :
    D.hessianOnFields f X Y x =
      g.inner x (D.connection (D.gradient f) x (X x)) (Y x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := D.metricCompatible.mvfderiv_inner_eq X
    ((D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)) hY
  change mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (Y y)) x (X x) =
    g.inner x (D.connection (D.gradient f) x (X x)) (Y x) +
      g.inner x (D.gradient f x) (D.connection Y x (X x)) at h
  simp only [D.inner_gradient] at h
  exact sub_eq_iff_eq_add.mpr h

theorem hessian_eq_inner_connection_gradient (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian f x u v = g.inner x (D.connection (D.gradient f) x u) v := by
  unfold hessian
  rw [D.hessianOnFields_eq_inner_connection_gradient hf _
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)]
  simp

theorem laplacian_eq_sum_inner_connection_gradient (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) :
    D.laplacian f x = ∑ i, g.inner x
      (D.connection (D.gradient f) x (g.orthonormalBasis x i))
      (g.orthonormalBasis x i) := by
  unfold laplacian
  simp_rw [D.hessian_eq_inner_connection_gradient hf]

theorem abs_mvfderiv_le_gradient_norm (D : LeviCivitaData g) (f : M → ℝ)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    |mvfderiv (𝓡 n) f x v| ≤ g.tangentNorm x (D.gradient f x) * g.tangentNorm x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← D.inner_gradient]
  exact abs_real_inner_le_norm (D.gradient f x) v

theorem gradient_norm_le_iff (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    {A : ℝ} (hA : 0 ≤ A) :
    g.tangentNorm x (D.gradient f x) ≤ A ↔
      ∀ v : TangentSpace (𝓡 n) x,
        |mvfderiv (𝓡 n) f x v| ≤ A * g.tangentNorm x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  constructor
  · intro h v
    exact (D.abs_mvfderiv_le_gradient_norm f x v).trans
      (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))
  · intro h
    have hh := h (D.gradient f x)
    rw [← D.inner_gradient] at hh
    change |inner ℝ (D.gradient f x) (D.gradient f x)| ≤ A * ‖D.gradient f x‖ at hh
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hh
    change ‖D.gradient f x‖ ≤ A
    nlinarith [norm_nonneg (D.gradient f x)]

theorem mvfderiv_gradient_normSq (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x v =
      2 * D.hessian f x v (D.gradient f x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgrad := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have h := D.metricCompatible.mvfderiv_inner_eq
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) hgrad hgrad
  change mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x) =
      g.inner x (D.connection (D.gradient f) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) (D.gradient f x) +
      g.inner x (D.gradient f x) (D.connection (D.gradient f) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) at h
  simp only [FiberBundle.extend_apply_self] at h
  rw [D.hessian_eq_inner_connection_gradient hf]
  rw [g.symm x (D.gradient f x)] at h
  linarith

end LeviCivitaData

end PoincareConjecture
