import PoincareConjecture.Proofs.M14.Sec6_6_RescalingGauges
import PoincareConjecture.Statements.M13Rescaling

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (S : GeneralizedFlowSpacetime n X time I)
  (D : ∀ t, SpacetimeSliceGeometry S t)
  (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

theorem rescalingSlicePoint (p : S.Point) :
    M13.parabolicSliceIdentification S D Q hQ a (S.timeFunction p)
      (spacetimeSlicePoint D p) =
        spacetimeSlicePoint (M13.parabolicSpacetimeSlice S D Q hQ a) p := by
  apply Subtype.ext
  exact M13.parabolicSliceIdentification_val S D Q hQ a _ _

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

theorem rescalingHorizontalScalar
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) (p : S.Point) :
    horizontalScalarCurvature L' p = Q⁻¹ * horizontalScalarCurvature L p := by
  have h := (rescalingSliceCalculus S D Q hQ a hM13 (S.timeFunction p)).scalar_eq
    (L.sliceConnection (S.timeFunction p))
    (L'.sliceConnection (parabolicTime Q a (S.timeFunction p))) (spacetimeSlicePoint D p)
  rw [rescalingSlicePoint] at h
  change horizontalScalarCurvature L' p = horizontalScalarCurvature L p / Q at h
  rw [h, div_eq_mul_inv, mul_comm]

end PoincareConjecture.M14
