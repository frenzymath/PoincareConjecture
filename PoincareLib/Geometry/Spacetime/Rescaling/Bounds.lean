import PoincareLib.Geometry.Spacetime.Rescaling.HorizontalCalculus

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Statements/M13ScaleBounds.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Quantitative invariance under the constructed rescaling

Morgan-Tian Definition 3.40, p. 61, Definition 9.1, p. 180, and the
scale changes in Section 9.2.1, p. 185. These are identities for supplied
domains and bounds. Existence of a noncollapsing configuration, estimates,
and limiting flows belong to later milestones.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

/-- Curvature and volume conditions on exactly corresponding actual sets. -/
structure ParabolicScaleBounds (P : ParabolicSpacetimeRescaling R Q hQ a) : Prop where
  curvature_bound : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (E : Set R.spacetime.Point) (K : ℝ),
    (∀ p ∈ E, horizontalCurvatureNorm D' p ≤ K / Q) ↔
      ∀ p ∈ E, horizontalCurvatureNorm D p ≤ K
  parabolic_curvature_bound : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (E : Set R.spacetime.Point) (r : ℝ) (_hr : 0 < r),
    (∀ p ∈ E, horizontalCurvatureNorm D' p ≤ 1 / (Real.sqrt Q * r) ^ 2) ↔
      ∀ p ∈ E, horizontalCurvatureNorm D p ≤ 1 / r ^ 2
  volume_bound : ∀ (t : ℝ) (x : (R.slices t).Point) (r κ : ℝ) (_hr : 0 < r) (_hκ : 0 < κ),
    (ENNReal.ofReal (κ * (Real.sqrt Q * r) ^ n) ≤
      calibratedMetricVolume (P.realization.slices (parabolicTime Q a t)).metricOnPoints
        ((P.realization.slices (parabolicTime Q a t)).metricOnPoints.ball
          (P.sliceIdentification t x) (Real.sqrt Q * r))) ↔
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume (R.slices t).metricOnPoints ((R.slices t).metricOnPoints.ball x r)
  scale_cutoff : ∀ (r r₀ : ℝ),
    (0 < Real.sqrt Q * r ∧ Real.sqrt Q * r ≤ Real.sqrt Q * r₀) ↔ 0 < r ∧ r ≤ r₀
  base_normalization : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (p : R.spacetime.Point), Q = horizontalScalarCurvature D p → a = R.spacetime.timeFunction p →
      P.realization.spacetime.timeFunction p = 0 ∧ horizontalScalarCurvature D' p = 1

end PoincareMT
