import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareCurve
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Differential.RectanglePartialTangent

/-!
# Smooth square densities of closed-time families

Morgan-Tian equation (6.2) and Lemma 6.22, pp. 106, 115-116.
The actual within time tangent and its horizontal projection are
jointly smooth through closed endpoints. Applying the metric and
scalar curvature gives the actual jointly smooth action density.
-/

set_option autoImplicit false
-- Product self-models and their charted-space instances are transported together.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Set ℝ} {U : Set E} {γ : ℝ × E → G.Point}

/-- The projected actual within time velocity of a smooth family is
jointly smooth on a closed-by-open rectangle, the velocity regularity
used in Lemma 6.22, pp. 115-116. -/
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
-- Smooth metric application elaborates two dependent actual velocity fields.
/-- The actual square density of a jointly smooth closed-time family
is jointly smooth, including its closed time endpoints, equation
(6.2) and Lemma 6.22, pp. 106, 115-116. -/
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

end PoincareMT.M14
