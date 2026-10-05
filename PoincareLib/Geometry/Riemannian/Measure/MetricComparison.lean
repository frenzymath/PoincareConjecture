import PoincareLib.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison

/-! # Volume comparison for ordered metrics

Pointwise comparison of quadratic forms compares the calibrated Riemannian
volume of every measurable set. This is the identity-map case of smooth
embedding volume comparison.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem volumeMeasure_le_of_inner_le (g h : RiemannianMetric n M)
    (hinner : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, h.inner x v v ≤ g.inner x v v)
    {A : Set M} (hA : MeasurableSet A) : h.volumeMeasure A ≤ g.volumeMeasure A := by
  have hbound : ∀ x ∈ (univ : Set M), ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm ((OpenPartialHomeomorph.refl M) x)
        (mfderiv (𝓡 n) (𝓡 n) (OpenPartialHomeomorph.refl M) x v) ≤
          (1 : ℝ) * g.tangentNorm x v := by
    intro x _ v
    change h.tangentNorm x (mfderiv (𝓡 n) (𝓡 n) id x v) ≤ 1 * g.tangentNorm x v
    simpa [RiemannianMetric.tangentNorm] using Real.sqrt_le_sqrt (hinner x v)
  simpa using g.volumeMeasure_image_le_of_tangentNorm_le h
    (OpenPartialHomeomorph.refl M) isOpen_univ (subset_refl _)
    contMDiff_id.contMDiffOn zero_lt_one hbound hA (subset_univ _)

end PoincareMT.RiemannianMetric
