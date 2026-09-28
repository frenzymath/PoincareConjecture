import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature.MovingJets

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

theorem limitNoncollapse_curvature_of_spatial_jets
    {α : Type*} {l : Filter α} [l.NeBot] {n : ℕ}
    {M : α → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} (D : ∀ k, LeviCivitaData (g k))
    (φ : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dh : LeviCivitaData h)
    (x : α → EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))
    (hφ : ∀ᶠ k in l, ∀ᶠ z in 𝓝 (x k),
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ (φ k) z ∧
        Function.Injective (mfderiv (𝓡 n) (𝓡 n) (φ k) z))
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin n,
      Tendsto (fun k ↦ iteratedFDeriv ℝ r (fun z ↦
        (g k).pullbackCoefficients (φ k) z
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) (x k)) l
        (𝓝 (iteratedFDeriv ℝ r (fun z ↦
          h.inner z (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b)) y))) :
    Tendsto (fun k ↦ (D k).curvatureTensorNorm (φ k (x k))) l
      (𝓝 (Dh.curvatureTensorNorm y)) := by
  exact LeviCivitaData.tendsto_curvatureTensorNorm_of_moving_scalar_pullback_jets
    D φ Dh x y hφ hjets

end PoincareConjecture.M47
