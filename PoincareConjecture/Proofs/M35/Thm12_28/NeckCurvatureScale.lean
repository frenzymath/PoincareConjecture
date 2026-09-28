import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvatureBound
import PoincareConjecture.Proofs.M13.OrdinaryFlow










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35



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

end PoincareConjecture.M35
