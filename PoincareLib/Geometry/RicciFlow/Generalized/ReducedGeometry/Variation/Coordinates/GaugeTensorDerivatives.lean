import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Basic
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality
import PoincareLib.Geometry.Riemannian.ScalarOperators.Hessian.Pullback
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.CurvatureTransport
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.CurvatureCalculus

/-!
# Gauge transport of the actual second-variation tensors

Morgan-Tian Lemma 6.14 and Proposition 6.33, pp. 111-112, 120-121,
in the generalized setting of Definition 3.36, pp. 60-61. The actual
slice local isometry transports the retained covariant Ricci derivative,
scalar Hessian and connection-time pairing, using M07 naturality and
M12's slice geometry. The gauge may have nonzero drift.
-/

set_option autoImplicit false
-- Identifying the time also identifies the selected dependent slice instances.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- Evaluate the retained horizontal Ricci derivative on a specified
equal time slice, Lemma 6.14 and Proposition 6.33, pp. 111-112, 120-121. -/
theorem horizontalRicciDerivativePairing_eq_slice (q : G.Point) {t : ℝ}
    (ht : G.spacetime.timeFunction q = t) (U V W : G.Horizontal q) :
    M14HorizontalRicciDerivativePairing G q U V W =
      (G.leafwise.sliceConnection t).covariantTensorDerivative
        (G.leafwise.sliceConnection t).ricciEvaluation ⟨q, ht⟩
        ![((G.slices t).tangentEquiv ⟨q, ht⟩).symm U,
          ((G.slices t).tangentEquiv ⟨q, ht⟩).symm V,
          ((G.slices t).tangentEquiv ⟨q, ht⟩).symm W] := by
  subst t
  rfl

/-- Evaluate the retained horizontal scalar Hessian on a specified
equal time slice, Proposition 6.33, pp. 120-121. -/
theorem horizontalHessianPairing_eq_slice (q : G.Point) {t : ℝ}
    (ht : G.spacetime.timeFunction q = t) (U V : G.Horizontal q) :
    M14HorizontalHessianPairing G q U V =
      (G.leafwise.sliceConnection t).hessian
        (G.leafwise.sliceConnection t).scalarCurvature ⟨q, ht⟩
        (((G.slices t).tangentEquiv ⟨q, ht⟩).symm U)
        (((G.slices t).tangentEquiv ⟨q, ht⟩).symm V) := by
  subst t
  rfl

variable {K : SpacetimeInterval} {T : SmoothSpacetimeInterval K}
  {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge G.spacetime T C}
  {g : MovingSpacetimeGaugeGeometry e} {c : MetricLeviCivitaFamily g.metric}
  (H : MovingGaugeCalculus G.leafwise g c)

include H

private theorem gauge_slice_inverse_tangent (t : T.Point) (x : C)
    (U : TangentSpace (𝓡 n) x) :
    ((G.slices t.val).tangentEquiv (movingGaugeSliceMap e G.slices t x)).symm
        (g.spatialTangentEquiv t x U) =
      mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e G.slices t) x U := by
  rw [← H.slice_tangent_eq t x U]
  exact ContinuousLinearEquiv.symm_apply_apply _ _

private theorem gauge_slice_invertible (t : T.Point) (x : C) :
    (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e G.slices t) x).IsInvertible := by
  rw [← (H.slice_localDiffeomorph t).mfderivToContinuousLinearEquiv_coe (by simp) x]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The spatial tangent equivalence transports the actual covariant
Ricci derivative in all three ordered slots, Lemma 6.14 and
Proposition 6.33, pp. 111-112, 120-121. -/
theorem movingGauge_ricciDerivativePairing (t : T.Point) (x : C)
    (U V W : TangentSpace (𝓡 n) x) :
    ricciDerivativePairing (c t.val) x U V W =
      M14HorizontalRicciDerivativePairing G (e.toSpacetime (t, x))
        (g.spatialTangentEquiv t x U) (g.spatialTangentEquiv t x V)
        (g.spatialTangentEquiv t x W) := by
  let f := movingGaugeSliceMap e G.slices t
  let D := G.leafwise.sliceConnection t.val
  have hmetric (y : C) (a b : TangentSpace (𝓡 n) y) :
      (g.metric t.val).inner y a b = (G.slices t.val).metricOnPoints.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b) :=
    (H.slice_metric_eq t y a b).symm
  have hricci (y : C) (v : Fin 2 → TangentSpace (𝓡 n) y) :
      (c t.val).ricciEvaluation y v =
        D.ricciEvaluation (f y) (fun i => mfderiv (𝓡 n) (𝓡 n) f y (v i)) :=
    (c t.val).ricci_eq_of_local_isometry D isOpen_univ
      (H.slice_localDiffeomorph t).contMDiff.contMDiffOn
      (fun y _ => hmetric y) (mem_univ y) (v 0) (v 1)
  have hd := (c t.val).covariantTensorDerivative_eq_pullback D
    ((H.slice_localDiffeomorph t).contMDiff x)
    (Eventually.of_forall (gauge_slice_invertible H t))
    (Eventually.of_forall hmetric)
    (c t.val).normalization_curvatureTensorCalculus.2.1
    D.normalization_curvatureTensorCalculus.2.1
    (Eventually.of_forall hricci) ![U, V, W]
  rw [horizontalRicciDerivativePairing_eq_slice _ (e.time_eq (t, x))]
  change ricciDerivativePairing (c t.val) x U V W =
    D.covariantTensorDerivative D.ricciEvaluation (f x)
      ![((G.slices t.val).tangentEquiv (f x)).symm (g.spatialTangentEquiv t x U),
        ((G.slices t.val).tangentEquiv (f x)).symm (g.spatialTangentEquiv t x V),
        ((G.slices t.val).tangentEquiv (f x)).symm (g.spatialTangentEquiv t x W)]
  rw [gauge_slice_inverse_tangent H t x U, gauge_slice_inverse_tangent H t x V,
    gauge_slice_inverse_tangent H t x W]
  unfold ricciDerivativePairing
  convert hd using 1
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The spatial tangent equivalence transports the retained scalar
curvature Hessian, Proposition 6.33, pp. 120-121. -/
theorem movingGauge_horizontalHessianPairing
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise)) (t : T.Point) (x : C)
    (U V : TangentSpace (𝓡 n) x) :
    (c t.val).hessian (c t.val).scalarCurvature x U V =
      M14HorizontalHessianPairing G (e.toSpacetime (t, x))
        (g.spatialTangentEquiv t x U) (g.spatialTangentEquiv t x V) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (G.slices t.val).Point :=
    (G.slices t.val).chartedSpace
  let f := movingGaugeSliceMap e G.slices t
  let D := G.leafwise.sliceConnection t.val
  have hscalarSlice : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ D.scalarCurvature := by
    have hi : ContMDiff (𝓡 n) (spacetimeModel n) ∞
        (Subtype.val : (G.slices t.val).Point → G.Point) :=
      (G.slices t.val).inclusion_smooth
    have hs := hscalar.comp hi
    have heq : horizontalScalarCurvature G.leafwise ∘
        (Subtype.val : (G.slices t.val).Point → G.Point) = D.scalarCurvature := by
      funext q
      exact horizontalScalarCurvature_eq_slice G.leafwise q.val q.property
    rwa [heq] at hs
  have heq : (c t.val).scalarCurvature = D.scalarCurvature ∘ f := by
    funext y
    exact (H.scalar_eq t y).trans
      (horizontalScalarCurvature_eq_slice G.leafwise _ (e.time_eq (t, y)))
  have hh := (c t.val).hessian_comp_of_metric_pullback D
    ((H.slice_localDiffeomorph t).contMDiff x)
    (Eventually.of_forall (gauge_slice_invertible H t))
    (Eventually.of_forall (fun y a b => (H.slice_metric_eq t y a b).symm))
    (hscalarSlice (f x)) U V
  rw [horizontalHessianPairing_eq_slice _ (e.time_eq (t, x))]
  change (c t.val).hessian (c t.val).scalarCurvature x U V =
    D.hessian D.scalarCurvature (f x)
      (((G.slices t.val).tangentEquiv (f x)).symm (g.spatialTangentEquiv t x U))
      (((G.slices t.val).tangentEquiv (f x)).symm (g.spatialTangentEquiv t x V))
  rw [gauge_slice_inverse_tangent H t x U, gauge_slice_inverse_tangent H t x V, heq]
  exact hh

/-- The three-term connection-time pairing is preserved by the same
spatial tangent equivalence, Claim 6.34, pp. 120-121, with the corrected
Jacobi tensor retained in the frozen contract. -/
theorem movingGauge_bcalPairing (t : T.Point) (x : C)
    (U V W : TangentSpace (𝓡 n) x) :
    backwardConnectionVariationPairing (c t.val) x U V W =
      M14BcalPairing G (e.toSpacetime (t, x))
        (g.spatialTangentEquiv t x U) (g.spatialTangentEquiv t x V)
        (g.spatialTangentEquiv t x W) := by
  simp only [backwardConnectionVariationPairing, M14BcalPairing,
    movingGauge_ricciDerivativePairing H]

end PoincareMT.M14
