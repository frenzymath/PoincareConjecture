import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Neck.Curvature.NeckCurvatureBound
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction

/-!
# Curvature bounds in the actual scalar-normalized neck

Morgan-Tian Definition 2.16, p. 30, and Theorem 12.28, pp. 323-324.
Positive metric scaling identifies the tensor in the frozen comparison
with the actual pullback of a genuine metric. M13's curvature transport
then returns the estimate to the original metric and normalization scale.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M35

/-- Definition 2.16, p. 30: actual metric homothety restores the specified
positive scale in the uniform central-sphere curvature estimate. -/
theorem exists_scaled_cylinder_curvature_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (A : StandardCylinderAtlas) (g : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g) (Q : ℝ), 0 < Q →
        ∀ (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x)
          (q : UnitTwoSphere), StandardSpatialCylinderClose A g epsilon Q N →
            D.curvatureTensorNorm (N.coordinate (q, 0)) < 2 * Q := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_cylinder_curvature_bound
  refine ⟨delta, hdelta, fun epsilon he hedelta A g D Q hQ x N q hclose => ?_⟩
  let G := M13.scaleSmoothMetric g Q hQ
  let DG := M13.scaleLeviCivitaData D Q hQ
  have hscaled : RoundCylinderClose epsilon 0
      (roundCylinderPullback G N.coordinate) := hclose
  have h := hbound epsilon he hedelta G DG x N q hscaled
  have hnorm := M13.homothety_curvatureTensorNorm_eq g G
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) D DG (N.coordinate (q, 0))
  change DG.curvatureTensorNorm (N.coordinate (q, 0)) =
    D.curvatureTensorNorm (N.coordinate (q, 0)) / Q at hnorm
  rw [hnorm] at h
  exact (div_lt_iff₀ hQ).mp h

/-- Theorem 12.28, pp. 323-324: the actual full curvature norm at every
sufficiently small static neck center is less than twice its scalar. -/
theorem exists_static_neck_curvature_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, epsilon ≤ delta →
      ∀ (A : StandardCylinderAtlas) (g : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g) (N : StandardStaticNeck A g D epsilon),
        D.curvatureTensorNorm N.center < 2 * D.scalarCurvature N.center := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_scaled_cylinder_curvature_bound
  refine ⟨delta, hdelta, fun epsilon hedelta A g D N => ?_⟩
  obtain ⟨q, hq⟩ := N.patch.center_sphere
  simpa only [hq] using hbound epsilon N.epsilon_pos hedelta A g D
    (D.scalarCurvature N.center) N.scalar_pos N.center N.patch q N.close

end PoincareMT.M35
