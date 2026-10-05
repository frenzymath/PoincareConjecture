import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients
import PoincareLib.Geometry.Riemannian.Curvature.Basic

/-!
# Orthonormal initial coordinate velocities

An orthonormal basis for the metric at the centre identifies its coordinate
velocity ellipsoid with a Euclidean ball. This is the normalization used in
the normal-coordinate construction of Morgan--Tian, Section 5.1,
Theorem 5.6, pp. 85--87.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The metric in its centre's chosen chart is the tangent metric itself. -/
theorem chartCoefficients_center (g : RiemannianMetric n M) (p : M)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) v w = g.inner p v w := by
  unfold pullbackCoefficients
  simp only [ContinuousLinearMap.bilinearComp_apply]
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := p)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  rw [hd]
  change g.inner ((extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p)) v w =
    g.inner p v w
  rw [extChartAt_to_inv]

open scoped Bundle in
/-- A linear change of initial coordinates makes the metric at the centre
exactly Euclidean, without a completeness assumption. -/
theorem exists_orthonormal_coordinate_frame (g : RiemannianMetric n M) (p : M) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  let b := (g.orthonormalBasis p).reindex (finCongr hdim)
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (show EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) from
      b.repr.symm.toLinearEquiv).toContinuousLinearEquiv
  refine ⟨L, fun v w => ?_⟩
  rw [g.chartCoefficients_center]
  change inner ℝ (b.repr.symm v) (b.repr.symm w) = inner ℝ v w
  exact b.repr.symm.inner_map_map v w

/-- Orthonormal initial derivative makes the actual pullback coefficients
Euclidean at the centre of the parametrization. -/
theorem pullbackCoefficients_zero_of_orthonormal
    (g : RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M}
    {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e 0) (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) :
    ∀ v w, g.pullbackCoefficients e 0 v w = inner ℝ v w := by
  have hchart : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (e 0) := by
    rw [he0]
    exact mdifferentiableAt_extChartAt (mem_chart_source _ _)
  have hd := mfderiv_comp 0 hchart (he.mdifferentiableAt (by simp))
  simp only [TangentSpace, mfderiv_eq_fderiv, Function.comp_def] at hd
  rw [hed.fderiv] at hd
  have hc : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (e 0) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    simp only [TangentSpace]
    rw [he0]
    exact mfderiv_extChartAt_self (I := 𝓡 n) (x := p)
  rw [hc, ContinuousLinearMap.id_comp] at hd
  intro v w
  unfold pullbackCoefficients
  simp only [ContinuousLinearMap.bilinearComp_apply]
  rw [← hd]
  change g.inner (e 0) (L v) (L w) = inner ℝ v w
  rw [he0, ← g.chartCoefficients_center]
  exact hL v w

end PoincareMT.RiemannianMetric
