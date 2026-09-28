import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Symmetry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.ParallelFrame



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

open CoordinateExponential ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def radialCurvatureOperator (g : RiemannianMetric n M) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  let c := extChartAt (𝓡 n) x
  let L := mfderiv (𝓡 n) (𝓡 n) c x
  L.inverse.comp ((jacobiCurvature (g.pullbackCoefficients c.symm) (c x) (L v)).comp L)

theorem radialCurvatureOperator_apply (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (x : M) (v u : TangentSpace (𝓡 n) x) :
    g.radialCurvatureOperator x v u = D.curvature x u v v := by
  have hx := mem_extChartAt_source (I := 𝓡 n) x
  have hcx := (extChartAt (𝓡 n) x).map_source hx
  have hB := (g.contDiffOn_chartCoefficients x).contDiffAt
    ((isOpen_extChartAt_target x).mem_nhds hcx)
  have hΓ := (contDiffAt_christoffelBilinear hB
    (g.isInvertible_chartCoefficients x hcx)).differentiableAt (by simp)
  change (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x) x).inverse
    (jacobiCurvature (g.pullbackCoefficients (extChartAt (𝓡 n) x).symm)
      (extChartAt (𝓡 n) x x) (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x) x v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x) x u)) = _
  rw [jacobiCurvature_apply hΓ, coordinateCurvature_in_chart g D x hx]
  exact (isInvertible_mfderiv_extChartAt hx).inverse_apply_self _


theorem radialCurvatureOperator_self (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 n) x) :
    g.radialCurvatureOperator x v v = 0 := by
  rw [g.radialCurvatureOperator_apply D]
  by_contra hne
  have h := g.pos x (D.curvature x v v v) hne
  have hz := D.curvatureTensor_zero_first x v (D.curvature x v v v) v
  exact (ne_of_gt h) hz


theorem isSymmetric_frame_radialCurvatureOperator
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (hP : ∀ u v, g.inner x (P u) (P v) = inner ℝ u v)
    (v : TangentSpace (𝓡 n) x) :
    LinearMap.IsSymmetric
      (P.symm.toContinuousLinearMap.comp
        ((g.radialCurvatureOperator x v).comp P.toContinuousLinearMap)).toLinearMap := by
  intro u w
  change inner ℝ (P.symm (g.radialCurvatureOperator x v (P u))) w =
    inner ℝ u (P.symm (g.radialCurvatureOperator x v (P w)))
  rw [← hP, ← hP, P.apply_symm_apply, P.apply_symm_apply,
    g.radialCurvatureOperator_apply D, g.radialCurvatureOperator_apply D]
  exact D.inner_radial_curvature_symm x (P u) v (P w)



theorem trace_transverse_frame_radialCurvatureOperator
    {m : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N] [IsManifold (𝓡 (m + 1)) ∞ N]
    (g : RiemannianMetric (m + 1) N) (D : LeviCivitaData g) (x : N)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (P : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] TangentSpace (𝓡 (m + 1)) x)
    (hP : ∀ u v, g.inner x (P u) (P v) = inner ℝ u v) :
    ((LinearMap.toMatrix b.toBasis b.toBasis
      (P.symm.toContinuousLinearMap.comp
        ((g.radialCurvatureOperator x (P (b 0))).comp P.toContinuousLinearMap)).toLinearMap
        ).submatrix Fin.succ Fin.succ).trace = D.ricci x (P (b 0)) (P (b 0)) := by
  rw [D.ricci_eq_transverse_curvature_trace x b P hP]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, LinearMap.toMatrix_apply, b.coe_toBasis,
    b.coe_toBasis_repr_apply, b.repr_apply_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply]
  change inner ℝ (b i.succ) (P.symm (g.radialCurvatureOperator x (P (b 0))
    (P (b j.succ)))) =
    g.inner x (D.curvature x (P (b j.succ)) (P (b 0)) (P (b 0))) (P (b i.succ))
  rw [← hP, P.apply_symm_apply, g.radialCurvatureOperator_apply D, g.symm]

theorem trace_transverse_frame_radialCurvatureOperator_of_isInvertible
    {m : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N] [IsManifold (𝓡 (m + 1)) ∞ N]
    (g : RiemannianMetric (m + 1) N) (D : LeviCivitaData g) (x : N)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (P : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] TangentSpace (𝓡 (m + 1)) x)
    (hi : P.IsInvertible)
    (hP : ∀ u v, g.inner x (P u) (P v) = inner ℝ u v) :
    ((LinearMap.toMatrix b.toBasis b.toBasis
      (P.inverse.comp ((g.radialCurvatureOperator x (P (b 0))).comp P) :
        EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).toLinearMap
        ).submatrix Fin.succ Fin.succ).trace = D.ricci x (P (b 0)) (P (b 0)) := by
  obtain ⟨Q, hQ⟩ := hi
  have hQa (u) : Q u = P u := congrArg (fun A => A u) hQ
  have hp : ∀ u v, g.inner x (Q u) (Q v) = inner ℝ u v := by
    intro u v
    simpa only [hQa] using hP u v
  have h := g.trace_transverse_frame_radialCurvatureOperator D x b Q hp
  have hQi : Q.symm.toContinuousLinearMap = P.inverse := by
    rw [← hQ, ContinuousLinearMap.inverse_equiv]
  simpa only [hQi, hQ, hQa] using h

end PoincareConjecture.RiemannianMetric
