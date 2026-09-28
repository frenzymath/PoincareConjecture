import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g₀ g₁ : RiemannianMetric n M} {h₀ h₁ : RiemannianMetric n N}

theorem connection_difference_eq_of_local_isometries
    (D₀ : LeviCivitaData g₀) (D₁ : LeviCivitaData g₁)
    (E₀ : LeviCivitaData h₀) (E₁ : LeviCivitaData h₁)
    {f : M → N} {x : M} (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric₀ : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g₀.inner y a b = h₀.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    (hmetric₁ : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g₁.inner y a b = h₁.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    (u v : TangentSpace (𝓡 n) x) :
    CovariantDerivative.difference D₀.connection D₁.connection x u v =
      (mfderiv (𝓡 n) (𝓡 n) f x).inverse
        (CovariantDerivative.difference E₀.connection E₁.connection (f x)
          (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v)) := by
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n))
    (mfderiv (𝓡 n) (𝓡 n) f x u)
  have hY := FiberBundle.mdifferentiableAt_extend (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) (mfderiv (𝓡 n) (𝓡 n) f x u)
  have hpY := hY.mpullback_vectorField (hf.of_le (by norm_cast))
    hinv.self_of_nhds le_rfl
  have hvalue : mpullback (𝓡 n) (𝓡 n) f Y x = u := by
    simp only [Y, mpullback_apply, FiberBundle.extend_apply_self,
      hinv.self_of_nhds.inverse_apply_self]
  have hsource := D₀.connection.isCovariantDerivativeOnUniv.difference_apply
    D₁.connection.isCovariantDerivativeOnUniv (mem_univ x) hpY
  have htarget := E₀.connection.isCovariantDerivativeOnUniv.difference_apply
    E₁.connection.isCovariantDerivativeOnUniv (mem_univ (f x)) hY
  have hs := congrArg (fun L => L v) hsource
  have ht := congrArg (fun L => L (mfderiv (𝓡 n) (𝓡 n) f x v)) htarget
  change CovariantDerivative.difference D₀.connection D₁.connection x
    (mpullback (𝓡 n) (𝓡 n) f Y x) v =
      D₀.connection (mpullback (𝓡 n) (𝓡 n) f Y) x v -
        D₁.connection (mpullback (𝓡 n) (𝓡 n) f Y) x v at hs
  change CovariantDerivative.difference E₀.connection E₁.connection (f x)
    (Y (f x)) (mfderiv (𝓡 n) (𝓡 n) f x v) =
      E₀.connection Y (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) -
        E₁.connection Y (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) at ht
  rw [hvalue, D₀.connection_mpullback_of_metric_pullback E₀ hf hinv hmetric₀ hY,
    D₁.connection_mpullback_of_metric_pullback E₁ hf hinv hmetric₁ hY, ← map_sub] at hs
  simpa only [Y, FiberBundle.extend_apply_self] using
    hs.trans (congrArg (mfderiv (𝓡 n) (𝓡 n) f x).inverse ht.symm)

theorem curvature_eq_of_local_isometry
    (D : LeviCivitaData g₀) (E : LeviCivitaData h₀)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      g₀.inner y a b = h₀.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    {x : M} (hx : x ∈ U) (hinv : (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w = (mfderiv (𝓡 n) (𝓡 n) f x).inverse
      (E.curvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g₀.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro z
  change g₀.inner x _ z = g₀.inner x _ z
  have h := D.curvatureTensor_eq_of_local_isometry E hU hf hmetric hx u v z w
  change g₀.inner x (D.curvature x u v w) z =
    h₀.inner (f x) (E.curvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w))
        (mfderiv (𝓡 n) (𝓡 n) f x z) at h
  rw [h, hmetric x hx, hinv.self_apply_inverse]

end PoincareConjecture.LeviCivitaData
