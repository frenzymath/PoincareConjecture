import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Connection.Transport
import Mathlib.Analysis.InnerProductSpace.LinearMap












set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Homothety

theorem inv_sqrt_mul_inv_sqrt (Q : ℝ) (hQ : 0 ≤ Q) :
    (Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ = Q⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hQ]

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]


noncomputable def homothetyTangentIsometry
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨h.toRiemannianMetric⟩
    TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) (f x) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hs : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  let e := (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (TangentSpace (𝓡 n) (f x))
      (Real.sqrt Q)⁻¹ (inv_ne_zero hs))
  apply e.isometryOfInner
  intro u v
  change h.inner (f x) ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x u)
    ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x v) = g.inner x u v
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [hf x u v]
  have hscale : (Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ * Q = 1 := by
    rw [inv_sqrt_mul_inv_sqrt Q hQ.le, inv_mul_cancel₀ hQ.ne']
  calc
    (Real.sqrt Q)⁻¹ * ((Real.sqrt Q)⁻¹ * (Q * g.inner x u v)) =
        ((Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ * Q) * g.inner x u v := by ring
    _ = g.inner x u v := by rw [hscale, one_mul]

theorem homothetyTangentIsometry_apply
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (x : M) (u : TangentSpace (𝓡 n) x) :
    homothetyTangentIsometry g h f Q hQ hf x u =
      (Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x u := rfl

end PoincareConjecture.Homothety
