import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry


set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem sectionalCurvature_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) (u v : TangentSpace (𝓡 n) x) :
    D.sectionalCurvature x u v = D'.sectionalCurvature (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  unfold sectionalCurvature
  rw [D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx,
    hmetric x hx u u, hmetric x hx v v, hmetric x hx u v]

theorem sectionalCurvature_lower_bound_iff_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) (κ : ℝ) :
    (∀ u v : TangentSpace (𝓡 n) x, κ ≤ D.sectionalCurvature x u v) ↔
      ∀ u v : TangentSpace (𝓡 n) (f x), κ ≤ D'.sectionalCurvature (f x) u v := by
  have hsurj := (g.mfderiv_bijective_of_pullback_eq h x
    (fun a b => (hmetric x hx a b).symm)).2
  constructor
  · intro hb u v
    obtain ⟨u', rfl⟩ := hsurj u
    obtain ⟨v', rfl⟩ := hsurj v
    rw [← D.sectionalCurvature_eq_of_local_isometry D' hU hf hmetric hx]
    exact hb u' v'
  · intro hb u v
    rw [D.sectionalCurvature_eq_of_local_isometry D' hU hf hmetric hx]
    exact hb _ _
end PoincareConjecture.LeviCivitaData
