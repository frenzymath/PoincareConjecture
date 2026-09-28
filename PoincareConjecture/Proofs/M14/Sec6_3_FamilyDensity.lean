import PoincareConjecture.Proofs.M14.Sec6_2_SquareCurve
import PoincareConjecture.Proofs.M14.Mathlib.RectanglePartialTangent

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Set ℝ} {U : Set E} {γ : ℝ × E → G.Point}

theorem squareFamilyVelocity_contMDiffOn (hC : UniqueDiffOn ℝ C) (hU : IsOpen U)
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E))) (spacetimeModel n) ∞ γ (C ×ˢ U)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × E => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (γ z)
        (projectedCurveVelocityWithin G (fun r => γ (r, z.2)) C z.1)) (C ×ˢ U) := by
  have htan := hγ.contMDiffOn_partialTangentWithin_fst_prod
    hC hU.uniqueDiffOn (1 : ℝ) (k := ∞) (by simp)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  exact hproj.comp_contMDiffOn htan

set_option maxHeartbeats 1000000 in

theorem squareFamilyDensity_contDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hC : UniqueDiffOn ℝ C) (hU : IsOpen U)
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, E))) (spacetimeModel n) ∞ γ (C ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E =>
      squareCurveDensity G (fun r => γ (r, z.2)) C z.1) (C ×ˢ U) := by
  have hα : ContMDiffOn (𝓘(ℝ, ℝ × E)) (spacetimeModel n) ∞ γ (C ×ˢ U) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hγ
  have hA : ContMDiffOn (𝓘(ℝ, ℝ × E))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × E => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (γ z)
        (projectedCurveVelocityWithin G (fun r => γ (r, z.2)) C z.1)) (C ×ˢ U) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact squareFamilyVelocity_contMDiffOn hC hU hγ
  have hmetric := G.spacetime.horizontalMetric.contMDiff.comp_contMDiffOn hα
  have hpair := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial G.Point ℝ) hA hA
  have hg : ContMDiffOn (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, ℝ)) ∞
      (fun z => G.spacetime.horizontalMetric.inner (γ z)
        (projectedCurveVelocityWithin G (fun r => γ (r, z.2)) C z.1)
        (projectedCurveVelocityWithin G (fun r => γ (r, z.2)) C z.1)) (C ×ˢ U) := by
    intro z hz
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
      using (Bundle.contMDiffWithinAt_totalSpace.mp (hpair z hz)).2
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar := (H.scalar_smooth.comp_contMDiffOn hα).contDiffOn
  exact ((contDiffOn_const.mul (contDiffOn_fst.pow 2)).mul hscalar).add
    (contDiffOn_const.mul hg.contDiffOn)

end PoincareConjecture.M14
