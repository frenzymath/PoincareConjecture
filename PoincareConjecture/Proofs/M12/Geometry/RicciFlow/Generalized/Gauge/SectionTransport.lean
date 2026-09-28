import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SectionTransport.TimeBracket
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SliceGeometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Restriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ s : ℝ, SpacetimeSliceGeometry F s}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

structure MovingGaugeSectionTransportFields
    (D : LeafwiseLeviCivitaFamily F S)
    (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric) : Prop where
  drift_smooth : ContMDiff (spacetimeModel n)
    ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
    (fun p : T.Point × C ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
      (E := (TangentSpace (𝓡 n) : C → Type _)) p.2 (movingGaugeDrift G p.1 p.2))
  leafwise_derivative_eq : ∀ (V : HorizontalSection F) (O : Set F.Point),
    IsOpen O → IsSmoothHorizontalSectionOn F V O →
    ∀ (t : T.Point) (x : C), e.toSpacetime (t, x) ∈ O →
    ∀ u : TangentSpace (𝓡 n) x,
      rawLeafwiseCovariantDerivative D V (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) =
      G.spatialTangentEquiv t x
        ((c t.val).connection (pullbackHorizontalSection G V t) x u)
  horizontal_derivative_eq : ∀ (V : HorizontalSection F) (O : Set F.Point),
    IsOpen O → IsSmoothHorizontalSectionOn F V O →
    ∀ (t : T.Point) (x : C), e.toSpacetime (t, x) ∈ O →
    ∀ (a : ℝ) (u : TangentSpace (𝓡 n) x),
      rawHorizontalCovariantDerivative D V (e.toSpacetime (t, x))
        (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
          (a • T.positiveTangent t, u)) =
      G.spatialTangentEquiv t x
        (a • movingGaugeSectionTimeDerivative G V t x +
          (c t.val).connection (pullbackHorizontalSection G V t) x u -
          a • (c t.val).connection (movingGaugeDrift G t) x
            (pullbackHorizontalSection G V t x))

private theorem movingGauge_drift_smooth
    (G : MovingSpacetimeGaugeGeometry e) :
    ContMDiff (spacetimeModel n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : T.Point × C ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := (TangentSpace (𝓡 n) : C → Type _)) p.2 (movingGaugeDrift G p.1 p.2)) := by
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  have hproj := (contMDiff_equivTangentBundleProd
    (I := 𝓡∂ 1) (M := T.Point) (I' := 𝓡 n) (M' := C) (n := ∞)).snd
  exact hproj.comp (movingGauge_liftedDrift_smooth e G)

private theorem rawLeafwiseCovariantDerivative_eq_slice
    (D : LeafwiseLeviCivitaFamily F S) (V : HorizontalSection F)
    (p : F.Point) {s : ℝ} (hs : F.timeFunction p = s) (w : F.Horizontal p) :
    rawLeafwiseCovariantDerivative D V p w =
      (S s).tangentEquiv ⟨p, hs⟩
        ((D.sliceConnection s).connection (restrictHorizontalSection S s V) ⟨p, hs⟩
          (((S s).tangentEquiv ⟨p, hs⟩).symm w)) := by
  subst s
  rfl

private theorem movingGauge_leafwise_derivative_eq
    (D : LeafwiseLeviCivitaFamily F S)
    (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (V : HorizontalSection F) (O : Set F.Point)
    (hO : IsOpen O) (hV : IsSmoothHorizontalSectionOn F V O)
    (t : T.Point) (x : C) (hx : e.toSpacetime (t, x) ∈ O)
    (u : TangentSpace (𝓡 n) x) :
    rawLeafwiseCovariantDerivative D V (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) =
      G.spatialTangentEquiv t x
        ((c t.val).connection (pullbackHorizontalSection G V t) x u) := by
  let f := movingGaugeSliceMap e S t
  have hlocal := movingGaugeSliceMap_localDiffeomorph e S G t
  have hinv (y : C) : (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible := by
    change (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) y).IsInvertible
    rw [← hlocal.mfderivToContinuousLinearEquiv_coe (by simp) y]
    exact ContinuousLinearMap.isInvertible_equiv
  have hpull : VectorField.mpullback (𝓡 n) (𝓡 n) f
      (restrictHorizontalSection S t.val V) = pullbackHorizontalSection G V t := by
    funext y
    apply (G.spatialTangentEquiv t y).injective
    rw [← movingGaugeSliceMap_tangent_eq e S G t y]
    change (S t.val).tangentEquiv (f y)
      (mfderiv (𝓡 n) (𝓡 n) f y
        ((mfderiv (𝓡 n) (𝓡 n) f y).inverse
          (restrictHorizontalSection S t.val V (f y)))) = _
    rw [(hinv y).self_apply_inverse]
    simp only [restrictHorizontalSection, pullbackHorizontalSection,
      ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      (G.metric t.val).inner y a b =
        (S t.val).metricOnPoints.inner (f y)
          (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b) := by
    exact Filter.Eventually.of_forall fun y a b =>
      ((movingGaugeSliceGeometryFields (S := S) e G).slice_metric_eq t y a b).symm
  have hY := (S t.val).restrictHorizontalSection_differentiableAt V (f x)
    ((hV.contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp))
  have hconn := (c t.val).connection_mpullback_of_metric_pullback
    (D.sliceConnection t.val) (hlocal.contMDiff x)
    (Filter.Eventually.of_forall hinv) hmetric hY u
  change (c t.val).connection
      (VectorField.mpullback (𝓡 n) (𝓡 n) f (restrictHorizontalSection S t.val V)) x u =
    (mfderiv (𝓡 n) (𝓡 n) f x).inverse
      ((D.sliceConnection t.val).connection (restrictHorizontalSection S t.val V) (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x u)) at hconn
  rw [hpull] at hconn
  rw [rawLeafwiseCovariantDerivative_eq_slice D V _ (e.time_eq (t, x))]
  rw [hconn, ← movingGaugeSliceMap_tangent_eq e S G t x]
  change (S t.val).tangentEquiv (f x)
      ((D.sliceConnection t.val).connection (restrictHorizontalSection S t.val V) (f x)
        (((S t.val).tangentEquiv (f x)).symm
          ((S t.val).tangentEquiv (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [← movingGaugeSliceMap_tangent_eq e S G t x]
  exact congrArg ((S t.val).tangentEquiv (f x))
    ((hinv x).self_apply_inverse _).symm

private theorem movingGauge_time_coefficient
    (e : MovingSpacetimeGauge F T C) (t : T.Point) (x : C)
    (a : ℝ) (u : TangentSpace (𝓡 n) x) :
    (mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction (e.toSpacetime (t, x)))
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (a • T.positiveTangent t, u)) = a := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  change (mfderiv (spacetimeModel n) 𝓘(ℝ) time (e.toSpacetime (t, x)))
    (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
      (a • T.positiveTangent t, u)) = a
  have hcomp := mfderiv_comp_apply (x := (t, x))
    (F.time_smooth.mdifferentiableAt (by simp))
    (e.smooth.mdifferentiableAt (by simp)) (a • T.positiveTangent t, u)
  have heq : time ∘ e.toSpacetime =
      (Subtype.val : T.Point → ℝ) ∘ Prod.fst := funext e.time_eq
  rw [heq] at hcomp
  rw [← hcomp, mfderiv_comp_apply (x := (t, x))
    (T.inclusion_smooth.mdifferentiableAt (by simp))
    (mdifferentiableAt_fst (I := 𝓡∂ 1) (I' := 𝓡 n))]
  simp only [mfderiv_fst]
  change (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : T.Point → ℝ) t)
    (a • T.positiveTangent t) = a
  rw [map_smul]
  rw [← T.inclusionDerivative_eq]
  change a • ((T.inclusionDerivative t) ((T.inclusionDerivative t).symm 1)) = a
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp

theorem movingGaugeSectionTransportFields
    (D : LeafwiseLeviCivitaFamily F S)
    (e : MovingSpacetimeGauge F T C)
    (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric) :
    MovingGaugeSectionTransportFields D G c := by
  refine ⟨movingGauge_drift_smooth G,
    movingGauge_leafwise_derivative_eq D G c, ?_⟩
  intro V O hO hV t x hx a u
  have hbracket := movingGauge_horizontalTimeBracket_eq e G c
    (movingGauge_drift_smooth G) V O hO hV t x hx
  change rawLeafwiseCovariantDerivative D V (e.toSpacetime (t, x))
      (F.horizontalProjection (e.toSpacetime (t, x))
        (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
          (a • T.positiveTangent t, u))) +
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction
        (e.toSpacetime (t, x))
        (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
          (a • T.positiveTangent t, u))) •
          horizontalTimeBracket F V (e.toSpacetime (t, x)) = _
  rw [movingGauge_projection_eq e G, movingGauge_time_coefficient e,
    movingGauge_leafwise_derivative_eq D G c V O hO hV t x hx, hbracket]
  rw [← map_smul, ← map_add]
  apply (G.spatialTangentEquiv t x).congr_arg
  rw [map_sub, map_smul, smul_sub, smul_add]
  abel

end PoincareConjecture
