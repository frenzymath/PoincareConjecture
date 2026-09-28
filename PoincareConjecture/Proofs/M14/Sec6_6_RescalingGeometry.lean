import PoincareConjecture.Proofs.M14.Sec6_6_RescalingLie
import PoincareConjecture.Proofs.M13.SliceConnection

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

noncomputable def rescalingLeafwise
    (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    LeafwiseLeviCivitaFamily (M13.parabolicSpacetime G.spacetime Q hQ a)
      (M13.parabolicSpacetimeSlice G.spacetime G.slices Q hQ a) :=
  M13.parabolicLeafwiseConnection G.leafwise Q hQ a

noncomputable def rescalingTransport
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    GeneralizedLGeometryTransport n X (fun p => parabolicTime Q a (time p))
      (parabolicInterval Q hQ a I) where
  spacetime := M13.parabolicSpacetime G.spacetime Q hQ a
  slices := M13.parabolicSpacetimeSlice G.spacetime G.slices Q hQ a
  timeIntervals := G.timeIntervals
  gaugeCover := rescalingGaugeCover G.spacetime G.timeIntervals G.gaugeCover Q hQ a
  leafwise := rescalingLeafwise G Q hQ a
  ricciEquation := by
    intro p v w
    obtain ⟨v, rfl⟩ := (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p).surjective v
    obtain ⟨w, rfl⟩ := (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p).surjective w
    have hL := (hM12.leafwise_calculus X time I G.spacetime G.slices
      G.timeIntervals G.gaugeCover).2 G.leafwise
    have hL' := (hM12.leafwise_calculus X _ _
      (M13.parabolicSpacetime G.spacetime Q hQ a)
      (M13.parabolicSpacetimeSlice G.spacetime G.slices Q hQ a) G.timeIntervals
      (rescalingGaugeCover G.spacetime G.timeIntervals G.gaugeCover Q hQ a)).2
      (rescalingLeafwise G Q hQ a)
    rw [rescalingHorizontalLie G.spacetime Q hQ a G.slices G.leafwise
      (rescalingLeafwise G Q hQ a) hL hL',
      rescalingHorizontalRicci G.spacetime G.slices Q hQ a G.leafwise
        (rescalingLeafwise G Q hQ a) hM13]
    exact G.ricciEquation p v w

theorem rescalingTransport_scalar
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : G.Point) :
    horizontalScalarCurvature (rescalingTransport hM12 hM13 G Q hQ a).leafwise p =
      Q⁻¹ * horizontalScalarCurvature G.leafwise p :=
  rescalingHorizontalScalar G.spacetime G.slices Q hQ a G.leafwise
    (rescalingLeafwise G Q hQ a) hM13 p

noncomputable def rescalingInitialEquiv
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) : S.Horizontal p ≃L[ℝ] (M13.parabolicSpacetime S Q hQ a).Horizontal p :=
  ContinuousLinearEquiv.equivOfInverse
    ((Real.sqrt Q)⁻¹ • (M13.parabolicSpacetimeHorizontal S Q hQ a p).toContinuousLinearMap)
    (Real.sqrt Q • (M13.parabolicSpacetimeHorizontal S Q hQ a p).symm.toContinuousLinearMap)
    (by intro v; simp [smul_smul, (Real.sqrt_pos.mpr hQ).ne'])
    (by intro v; simp [smul_smul, (Real.sqrt_pos.mpr hQ).ne'])

theorem rescalingInitialEquiv_inner
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) (v w : S.Horizontal p) :
    (M13.parabolicSpacetime S Q hQ a).horizontalMetric.inner p
      (rescalingInitialEquiv S Q hQ a p v) (rescalingInitialEquiv S Q hQ a p w) =
        S.horizontalMetric.inner p v w := by
  change (M13.parabolicSpacetime S Q hQ a).horizontalMetric.inner p
    ((Real.sqrt Q)⁻¹ • M13.parabolicSpacetimeHorizontal S Q hQ a p v)
    ((Real.sqrt Q)⁻¹ • M13.parabolicSpacetimeHorizontal S Q hQ a p w) = _
  simp only [map_smul, smul_apply, smul_eq_mul, M13.parabolicSpacetime_metric]
  have hs : (Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ * Q = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hQ.le, inv_mul_cancel₀ hQ.ne']
  calc
    _ = ((Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ * Q) *
        S.horizontalMetric.inner p v w := by ring
    _ = _ := by rw [hs, one_mul]

end PoincareConjecture.M14
