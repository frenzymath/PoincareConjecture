import PoincareConjecture.Proofs.M10.MetricTrace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.MetricCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem metricCoordinates_inner (g : RiemannianMetric n M) (q : M)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.inner q (metricCoordinates g q v) (metricCoordinates g q w) = inner ℝ v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (metricCoordinates g q).inner_map_map v w

theorem metricCoordinates_basis_inner (g : RiemannianMetric n M) (q : M) (i j : Fin n) :
    g.inner q (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        if i = j then 1 else 0 := by
  rw [metricCoordinates_inner]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i j

set_option backward.isDefEq.respectTransparency false in

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

theorem sum_metricCoordinates_ricci (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (q : M) :
    (∑ i : Fin n, D.ricci q
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))) =
        D.scalarCurvature q :=
  sum_metricCoordinates_basis g q (fun v ↦ D.ricci q v v)

theorem sum_metricCoordinates_hessian (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (f : M → ℝ) (q : M) :
    (∑ i : Fin n, D.hessian f q
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))
      (metricCoordinates g q (EuclideanSpace.basisFun (Fin n) ℝ i))) =
        D.laplacian f q :=
  sum_metricCoordinates_basis g q (fun v ↦ D.hessian f q v v)

end PoincareConjecture.SurgeryVolume.Measure
