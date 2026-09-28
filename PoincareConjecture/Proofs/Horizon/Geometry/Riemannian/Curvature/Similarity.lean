import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import Mathlib.Geometry.Manifold.Diffeomorph







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture.LeviCivitaData

theorem sectionalCurvature_eq_of_metric_similarity
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) {a : ℝ} (ha : 0 < a)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = a * g.inner x v w)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    D'.sectionalCurvature (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
      (mfderiv (𝓡 n) (𝓡 n) e x w) = a⁻¹ * D.sectionalCurvature x v w := by
  let G := rescaledMetric g a ha
  let DS := rescaledMetric_connection g D a ha
  have hm : ∀ x ∈ (univ : Set M), ∀ v w : TangentSpace (𝓡 n) x,
      G.inner x v w = h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) := fun x _ v w => (hmetric x v w).symm
  have ht := DS.curvatureTensor_eq_of_local_isometry D' isOpen_univ
    e.contMDiff.contMDiffOn hm (mem_univ x) v w v w
  calc
    D'.sectionalCurvature (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) =
        DS.sectionalCurvature x v w := by
      unfold sectionalCurvature
      rw [← ht, ← hm x (mem_univ x) v v, ← hm x (mem_univ x) w w,
        ← hm x (mem_univ x) v w]
    _ = _ := rescaledMetric_sectionalCurvature g D a ha x v w
end PoincareConjecture.LeviCivitaData


theorem PoincareConjecture.LeviCivitaData.sectionalCurvature_lower_bound_of_metric_similarity
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {g : PoincareConjecture.RiemannianMetric n M} {h : PoincareConjecture.RiemannianMetric n N}
    (D : PoincareConjecture.LeviCivitaData g) (D' : PoincareConjecture.LeviCivitaData h)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) {a : ℝ} (ha : 0 < a)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = a * g.inner x v w)
    {K : M → ℝ}
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -K x ≤ D.sectionalCurvature x v w) :
    ∀ y (v w : TangentSpace (𝓡 n) y),
      -(a⁻¹ * K (e.symm y)) ≤ D'.sectionalCurvature y v w := by
  intro y v w
  obtain ⟨x, rfl⟩ := e.surjective y
  have hb := (PoincareConjecture.rescaledMetric g a ha).mfderiv_bijective_of_pullback_eq
    h x (hmetric x)
  obtain ⟨v', rfl⟩ := hb.2 v
  obtain ⟨w', rfl⟩ := hb.2 w
  change -(a⁻¹ * K (e.symm (e x))) ≤ D'.sectionalCurvature (e x)
    (mfderiv (𝓡 n) (𝓡 n) e x v') (mfderiv (𝓡 n) (𝓡 n) e x w')
  rw [e.symm_apply_apply, D.sectionalCurvature_eq_of_metric_similarity D' e ha hmetric]
  have ht := mul_le_mul_of_nonneg_left (hsec x v' w') (inv_nonneg.mpr ha.le)
  simpa only [mul_neg] using ht
