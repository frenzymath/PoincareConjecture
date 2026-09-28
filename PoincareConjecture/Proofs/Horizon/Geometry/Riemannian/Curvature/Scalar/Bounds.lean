import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {g : RiemannianMetric n M}

theorem ricci_le_scalarCurvature_mul_inner_of_nonneg
    (D : LeviCivitaData g) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (v : TangentSpace (𝓡 n) x) :
    D.ricci x v v ≤ D.scalarCurvature x * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let Ric := fun i j => D.ricci x (b i) (b j)
  have hquad : ∀ w : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ,
      0 ≤ ∑ i, ∑ j, Ric i j * w i * w j := by
    intro w
    let z := b.repr.symm (WithLp.toLp 2 w)
    have h := hRic z
    rw [D.ricci_eq_sum_frame] at h
    have hcoord (i) : g.inner x (b i) z = w i := by
      change inner ℝ (b i) (b.repr.symm (WithLp.toLp 2 w)) = w i
      rw [← b.repr_apply_apply, b.repr.apply_symm_apply]
    simpa only [hcoord, Ric, b] using h
  have h := Poincare.LinearAlgebra.quadratic_le_trace_mul_sum_sq Ric hquad
    (fun i => inner ℝ (b i) v)
  have hnorm : (∑ i, (inner ℝ (b i) v) ^ 2) = g.inner x v v := by
    rw [b.sum_sq_inner_right]
    exact (real_inner_self_eq_norm_sq v).symm
  have hcoord := D.ricci_eq_sum_frame x v v
  change D.ricci x v v = ∑ i, ∑ j, Ric i j * inner ℝ (b i) v *
    inner ℝ (b j) v at hcoord
  rw [← hcoord, hnorm] at h
  exact h

end PoincareConjecture.LeviCivitaData
