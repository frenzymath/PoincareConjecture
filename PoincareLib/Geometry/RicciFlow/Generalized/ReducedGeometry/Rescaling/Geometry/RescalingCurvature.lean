import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ParabolicRescaling
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Geometry.RescalingGauges
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory

/-!
# Actual slice curvature under bare spacetime rescaling

Morgan-Tian Definition 3.40, p. 61, and Lemma 6.72, p. 141.
The supplied metric-homothety calculus applies to the selected slice
connections, so Ricci and scalar transport do not require a new atlas.
-/

set_option autoImplicit false
-- Slice-point aliases must unfold when matching the transported horizontal fibers.
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (S : GeneralizedFlowSpacetime n X time I)
  (D : ∀ t, SpacetimeSliceGeometry S t)
  (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

/-- The actual rescaled slice identification sends the canonical slice
point to the same spacetime point. Definition 3.40, p. 61. -/
theorem rescalingSlicePoint (p : S.Point) :
    M13.parabolicSliceIdentification S D Q hQ a (S.timeFunction p)
      (spacetimeSlicePoint D p) =
        spacetimeSlicePoint (M13.parabolicSpacetimeSlice S D Q hQ a) p := by
  apply Subtype.ext
  exact M13.parabolicSliceIdentification_val S D Q hQ a _ _

/-- The inverse slice tangent identification commutes with the actual
rescaled horizontal map. Definition 3.40, p. 61. -/
theorem rescalingSliceTangent (p : S.Point) (v : S.Horizontal p) :
    mfderiv (𝓡 n) (𝓡 n)
      (M13.parabolicSliceIdentification S D Q hQ a (S.timeFunction p))
      (spacetimeSlicePoint D p)
      (((D (S.timeFunction p)).tangentEquiv (spacetimeSlicePoint D p)).symm v) =
      (((M13.parabolicSpacetimeSlice S D Q hQ a
        ((M13.parabolicSpacetime S Q hQ a).timeFunction p))).tangentEquiv
        (spacetimeSlicePoint (M13.parabolicSpacetimeSlice S D Q hQ a) p)).symm
          (M13.parabolicSpacetimeHorizontal S Q hQ a p v) := by
  apply ((M13.parabolicSpacetimeSlice S D Q hQ a
    ((M13.parabolicSpacetime S Q hQ a).timeFunction p)).tangentEquiv
      (spacetimeSlicePoint (M13.parabolicSpacetimeSlice S D Q hQ a) p)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Subtype.ext
  have h := M13.parabolicSliceIdentification_tangent S D Q hQ a (S.timeFunction p)
    (spacetimeSlicePoint D p)
    (((D (S.timeFunction p)).tangentEquiv (spacetimeSlicePoint D p)).symm v)
  rw [rescalingSlicePoint] at h
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

/-- Apply the supplied M13 calculus to the selected actual slices and
their actual homothety, Definition 3.40, p. 61. -/
theorem rescalingSliceCalculus (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (t : ℝ) :
    MetricHomothetyCalculus (D t).metricOnPoints
      (M13.parabolicSpacetimeSlice S D Q hQ a (parabolicTime Q a t)).metricOnPoints
      (M13.parabolicSliceIdentification S D Q hQ a t) Q :=
  hM13.metric_homothety (D t).Point
    (M13.parabolicSpacetimeSlice S D Q hQ a (parabolicTime Q a t)).Point
    (D t).metricOnPoints
    (M13.parabolicSpacetimeSlice S D Q hQ a (parabolicTime Q a t)).metricOnPoints
    (M13.parabolicSliceIdentification S D Q hQ a t) Q hQ
    (M13.parabolicSliceIdentification_metric S D Q hQ a t)

variable (L : LeafwiseLeviCivitaFamily S D)
  (L' : LeafwiseLeviCivitaFamily (M13.parabolicSpacetime S Q hQ a)
    (M13.parabolicSpacetimeSlice S D Q hQ a))

/-- Four-covariant horizontal curvature gains the metric factor under
parabolic rescaling, Definition 3.40, p. 61. -/
theorem rescalingHorizontalRiemann
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (p : S.Point) (v w z q : S.Horizontal p) :
    horizontalRiemann L' p (M13.parabolicSpacetimeHorizontal S Q hQ a p v)
      (M13.parabolicSpacetimeHorizontal S Q hQ a p w)
      (M13.parabolicSpacetimeHorizontal S Q hQ a p z)
      (M13.parabolicSpacetimeHorizontal S Q hQ a p q) =
        Q * horizontalRiemann L p v w z q := by
  let x := spacetimeSlicePoint D p
  let j := (D (S.timeFunction p)).tangentEquiv x
  have h := (rescalingSliceCalculus S D Q hQ a hM13 (S.timeFunction p)).riemann_eq
    (L.sliceConnection (S.timeFunction p))
    (L'.sliceConnection (parabolicTime Q a (S.timeFunction p))) x
    (j.symm v) (j.symm w) (j.symm z) (j.symm q)
  dsimp only [x, j] at h
  erw [rescalingSlicePoint, rescalingSliceTangent S D Q hQ a p v,
    rescalingSliceTangent S D Q hQ a p w, rescalingSliceTangent S D Q hQ a p z,
    rescalingSliceTangent S D Q hQ a p q] at h
  exact h

/-- Horizontal Ricci is invariant under a positive constant metric
homothety, as used in Lemma 6.72, p. 141. -/
theorem rescalingHorizontalRicci
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (p : S.Point) (v w : S.Horizontal p) :
    horizontalRicci L' p (M13.parabolicSpacetimeHorizontal S Q hQ a p v)
      (M13.parabolicSpacetimeHorizontal S Q hQ a p w) = horizontalRicci L p v w := by
  let x := spacetimeSlicePoint D p
  let j := (D (S.timeFunction p)).tangentEquiv x
  have h := (rescalingSliceCalculus S D Q hQ a hM13 (S.timeFunction p)).ricci_eq
    (L.sliceConnection (S.timeFunction p))
    (L'.sliceConnection (parabolicTime Q a (S.timeFunction p))) x (j.symm v) (j.symm w)
  dsimp only [x, j] at h
  erw [rescalingSlicePoint, rescalingSliceTangent S D Q hQ a p v,
    rescalingSliceTangent S D Q hQ a p w] at h
  exact h

/-- Scalar curvature has weight minus one under parabolic rescaling,
Lemma 6.72, p. 141. -/
theorem rescalingHorizontalScalar
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) (p : S.Point) :
    horizontalScalarCurvature L' p = Q⁻¹ * horizontalScalarCurvature L p := by
  have h := (rescalingSliceCalculus S D Q hQ a hM13 (S.timeFunction p)).scalar_eq
    (L.sliceConnection (S.timeFunction p))
    (L'.sliceConnection (parabolicTime Q a (S.timeFunction p))) (spacetimeSlicePoint D p)
  rw [rescalingSlicePoint] at h
  change horizontalScalarCurvature L' p = horizontalScalarCurvature L p / Q at h
  rw [h, div_eq_mul_inv, mul_comm]

end PoincareMT.M14
