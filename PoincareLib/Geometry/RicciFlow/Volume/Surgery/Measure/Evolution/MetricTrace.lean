import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.MetricCoordinates
import PoincareLib.Geometry.Riemannian.ScalarOperators

/-!
Adapted from Mapher `PoincareMT/Proofs/M10/MetricTrace.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Traces in the fixed metric coordinates

The source normalization uses the selected metric's actual orthonormal basis,
reindexed by Fin n. These identities retain that selection in both geometric
traces used in the Jacobian evolution.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- Fixed metric coordinates preserve the literal selected inner product. -/
theorem metricCoordinates_inner (g : RiemannianMetric n M) (q : M)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.inner q (metricCoordinates g q v) (metricCoordinates g q w) = inner ℝ v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (metricCoordinates g q).inner_map_map v w

/-- The Gram matrix of the selected coordinate basis is the identity. -/
theorem metricCoordinates_basis_inner (g : RiemannianMetric n M) (q : M) (i j : Fin n) :
    g.inner q (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        if i = j then 1 else 0 := by
  rw [metricCoordinates_inner]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i j

set_option backward.isDefEq.respectTransparency false in
/-- Summing over the fixed coordinates is summing over the exact selected orthonormal basis. -/
theorem sum_metricCoordinates_basis (g : RiemannianMetric n M) (q : M)
    (f : TangentSpace (𝓡 n) q → ℝ) :
    (∑ i : Fin n, f (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))) =
      ∑ i, f (g.orthonormalBasis q i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  simp only [metricCoordinates, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.repr_symm_single, OrthonormalBasis.reindex_apply]
  exact Equiv.sum_comp (finCongr hdim).symm (fun i ↦ f (g.orthonormalBasis q i))

/-- The Ricci trace in the fixed orthonormal coordinates is the selected scalar curvature. -/
theorem sum_metricCoordinates_ricci (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (q : M) :
    (∑ i : Fin n, D.ricci q
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))) =
        D.scalarCurvature q :=
  sum_metricCoordinates_basis g q (fun v ↦ D.ricci q v v)

/-- The Hessian trace in the same fixed coordinates is the literal frozen Laplacian. -/
theorem sum_metricCoordinates_hessian (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (f : M → ℝ) (q : M) :
    (∑ i : Fin n, D.hessian f q
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))) =
        D.laplacian f q :=
  sum_metricCoordinates_basis g q (fun v ↦ D.hessian f q v v)

end PoincareMT.SurgeryVolume.Measure
