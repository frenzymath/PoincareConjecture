import PoincareConjecture.Proofs.M35.Thm12_28.NeckBackwardCurvature
import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvatureScale










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35



theorem exists_spacetime_neck_curvature_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (A : StandardCylinderAtlas) (g : ℝ → RiemannianMetric 3 StandardCapSpace)
        (D : ∀ t, LeviCivitaData (g t)) (origin Q : ℝ), 0 < Q →
        ∀ (I : Set ℝ) (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x),
          StandardSpacetimeCylinderClose A g epsilon origin Q I N →
          ∀ u ∈ I ∩ Icc (-1 : ℝ) 0, ∀ y ∈ N.carrier,
            (D (origin + u / Q)).curvatureTensorNorm y < 2 * Q := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_backward_neck_carrier_curvature_bound
  refine ⟨delta, hdelta, fun epsilon he hedelta A g D origin Q hQ I x N hclose u hu y hy => ?_⟩
  let t := origin + u / Q
  let G := M13.scaleSmoothMetric (g t) Q hQ
  let DG := M13.scaleLeviCivitaData (D t) Q hQ
  have hc : RoundCylinderClose epsilon u (roundCylinderPullback G N.coordinate) := by
    obtain ⟨hsmooth, b, hb, hjet⟩ := hclose
    exact ⟨hsmooth u hu.1, b, hb, hjet u hu.1⟩
  have h := hbound epsilon he hedelta u hu.2 G DG x N hc y hy
  have hnorm := M13.homothety_curvatureTensorNorm_eq (g t) G
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
    (M13.identity_metricHomothety (g t) Q hQ) (D t) DG y
  change DG.curvatureTensorNorm y = (D t).curvatureTensorNorm y / Q at hnorm
  rw [hnorm] at h
  exact (div_lt_iff₀ hQ).mp h




theorem exists_evolving_neck_curvature_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, epsilon ≤ delta →
      ∀ (A : StandardCylinderAtlas) (g₀ : StandardInitialMetric)
        (F : MaximalStandardCapFlow g₀) (t : ℝ) (x : StandardCapSpace) (I : Set ℝ)
        (N : StandardEvolvingNeck A F t epsilon x I),
        ∀ u ∈ I ∩ Icc (-1 : ℝ) 0, ∀ y ∈ N.patch.carrier,
          (F.connection (t + u / (F.connection t).scalarCurvature x)).curvatureTensorNorm y <
            2 * (F.connection t).scalarCurvature x := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_spacetime_neck_curvature_bound
  refine ⟨delta, hdelta, fun epsilon hedelta A g₀ F t x I N => ?_⟩
  exact hbound epsilon N.epsilon_pos hedelta A F.metric F.connection t
    ((F.connection t).scalarCurvature x) N.scalar_pos I x N.patch N.close

end PoincareConjecture.M35
