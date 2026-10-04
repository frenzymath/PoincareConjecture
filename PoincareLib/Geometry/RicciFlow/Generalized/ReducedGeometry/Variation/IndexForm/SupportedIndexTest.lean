import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Extension.SupportedAffineField
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.IndexAffine

/-!
# Supported tests for a zero-index variation

Morgan-Tian Proposition 6.13, Lemma 6.14 and Corollary 6.16,
pp. 110-112. Actual admissible affine perturbations and positivity
annihilate the mixed index form. Green's identity then gives the
vanishing integral of the corrected Jacobi residual against every
supported gauge test field.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

variable (hCoordinates : M12MetricPredecessors.{0} n)
  (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
  (hmin : M14IsMinimizing p) (hfix : M14BothEndpointsFixed V)
  (hzero : M14SecondVariationIndexForm V D = 0)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))
  {U : Set G.Point} (hU : IsOpen U)
  (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
  (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
  (hη : ContDiff ℝ ∞ η)
  (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
  (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U)
  (Z : M14LVariationData G p R)
  (hZ : ∀ s v, Z.squareFamily s v = supportedGaugeFamily R b lift η (s, v))
  (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
    (M14VariationField Z))

include hCoordinates hM04 hM12 hmin hfix hzero hU hlift hright hη hsupport hsrc hZ EZ

/-- A zero-index fixed-endpoint variation at a minimizing path
annihilates every actual supported gauge test in the mixed index form,
Proposition 6.13 and Corollary 6.16, pp. 110-112. -/
theorem index_pair_supportedGauge_eq_zero :
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      pullbackIndexPairDensity R D.variation_extension EZ s) = 0 := by
  apply index_pair_zero_of_affine_variations hCoordinates hM04 hM12 V D hmin hzero
    (M14VariationField Z) EZ
  intro c
  obtain ⟨W, hfixW, hW⟩ := exists_supportedAffineGauge_variation V b lift η c hM12 hfix
    hU hlift hright hη hsupport hsrc
  refine ⟨W, hfixW, fun s hs => ?_⟩
  exact variationField_supportedAffineGauge_eq V W b lift η c Z hW hZ hU hlift hright hη
    hsupport hsrc hs

/-- Green's identity turns the vanishing mixed index into a zero
integral of the actual Jacobi residual, retaining the supplied first
extension exactly, Proposition 6.13 and Lemma 6.14, pp. 110-112. -/
theorem jacobiResidual_supportedGauge_integral_eq_zero (hfixZ : M14BothEndpointsFixed Z) :
    let Q := jacobiFieldDataOfExtension
      (hM12.coordinate_gauges X time I G.spacetime G.slices
        G.timeIntervals G.gaugeCover G.leafwise) D.variation_extension
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      M14JacobiResidual G R Q s (M14VariationField Z s)) = 0 := by
  dsimp only
  let Q := jacobiFieldDataOfExtension
    (hM12.coordinate_gauges X time I G.spacetime G.slices
      G.timeIntervals G.gaugeCover G.leafwise) D.variation_extension
  have hpair := index_pair_supportedGauge_eq_zero hCoordinates hM04 hM12 V D hmin hfix hzero
    b lift η hU hlift hright hη hsupport hsrc Z hZ EZ
  have hG := integral_pullbackIndexPairDensity R Q EZ hM04 hM12
  obtain ⟨hleft, hrightZ⟩ := variationField_fixed_endpoints_eq_zero Z hfixZ
  change (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
    pullbackIndexPairDensity R Q.extension EZ s) = 0 at hpair
  rw [hpair] at hG
  simp only [pullbackIndexBoundaryPair, hleft, hrightZ, map_zero, sub_self, zero_sub] at hG
  exact (neg_eq_zero.mp hG.symm)

end PoincareMT.M14
