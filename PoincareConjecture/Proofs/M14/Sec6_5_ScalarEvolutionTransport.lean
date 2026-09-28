import PoincareConjecture.Proofs.M14.Sec6_5_ScalarEvolutionTransportSlice
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.MetricDerivative.Time
import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Statements.Ch04.CurvatureTheory










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem backwardScalarReaction_eq_slice (q : G.Point) {t : ℝ}
    (ht : G.spacetime.timeFunction q = t) :
    -(G.leafwise.sliceConnection (G.spacetime.timeFunction q)).laplacian
        (G.leafwise.sliceConnection (G.spacetime.timeFunction q)).scalarCurvature
        (spacetimeSlicePoint G.slices q) -
      2 * (G.leafwise.sliceConnection (G.spacetime.timeFunction q)).ricciNormSq
        (spacetimeSlicePoint G.slices q) =
    -(G.leafwise.sliceConnection t).laplacian
        (G.leafwise.sliceConnection t).scalarCurvature ⟨q, ht⟩ -
      2 * (G.leafwise.sliceConnection t).ricciNormSq ⟨q, ht⟩ := by
  subst t
  rfl




theorem ordinaryGauge_backwardScalarEvolution (b : G.gaugeCover.index)
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hscalar : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞
      (horizontalScalarCurvature G.leafwise))
    (W : OrdinaryGaugeWitness G.leafwise
      (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x : G.gaugeCover.spatial b) :
    M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
        ((G.gaugeCover.cylinder b).toSpacetime (t, x)) =
      -(G.leafwise.sliceConnection t.val).laplacian
          (G.leafwise.sliceConnection t.val).scalarCurvature
          (movingGaugeSliceMap (G.gaugeCover.cylinder b).toMovingSpacetimeGauge
            G.slices t x) -
        2 * (G.leafwise.sliceConnection t.val).ricciNormSq
          (movingGaugeSliceMap (G.gaugeCover.cylinder b).toMovingSpacetimeGauge
            G.slices t x) := by
  let K := G.gaugeCover.interval b
  let T := G.timeIntervals.interval K
  let e := (G.gaugeCover.cylinder b).toMovingSpacetimeGauge
  have H := ordinaryGauge_movingCalculus b hCoordinates W
  have hd := movingGauge_hasDerivWithinAt_comp e t x
    (hscalar.mdifferentiableAt (by simp))
  have heq (s : ℝ) (hs : s ∈ K.domain) :
      (W.flow.connection s).scalarCurvature x =
        horizontalScalarCurvature G.leafwise (e.toSpacetime (T.realParam s, x)) := by
    have h := H.scalar_eq (T.realParam s) x
    rwa [T.realParam_val hs] at h
  have hd' := hd.congr heq (heq t.val t.property)
  have ho := hM04.scalar_evolution n (G.gaugeCover.spatial b) K.domain
    W.flow t.val t.property x
  have hderiv := (uniqueDiffWithinAt_of_spacetimeInterval K t).eq_deriv K.domain hd' ho
  have hvelocity : movingGaugeTimeVelocity e t x =
      G.spacetime.timeVector ((G.gaugeCover.cylinder b).toSpacetime (t, x)) := by
    unfold movingGaugeTimeVelocity
    rw [mfderiv_prod_eq_add_apply (e.smooth.mdifferentiableAt (by simp)),
      map_zero, add_zero]
    exact (G.gaugeCover.cylinder b).worldline_derivative t x
  rw [hvelocity] at hderiv
  calc
    _ = -((W.flow.connection t.val).laplacian (W.flow.connection t.val).scalarCurvature x +
        2 * (W.flow.connection t.val).ricciNormSq x) :=
      congrArg (fun r : ℝ => -r) hderiv
    _ = _ := by
      rw [movingGauge_scalarLaplacian H hscalar t x, movingGauge_ricciNormSq H t x]
      ring




theorem backwardScalarEvolution (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (q : G.Point) :
    let D := G.leafwise.sliceConnection (G.spacetime.timeFunction q)
    let qs := spacetimeSlicePoint G.slices q
    M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) q =
      -D.laplacian D.scalarCurvature qs - 2 * D.ricciNormSq qs := by
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  obtain ⟨b, ⟨t, x⟩, rfl⟩ := G.gaugeCover.covers q
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  dsimp only
  rw [backwardScalarReaction_eq_slice _ ((G.gaugeCover.cylinder b).time_eq (t, x))]
  exact ordinaryGauge_backwardScalarEvolution b hCoordinates hM04 hscalar W t x

end PoincareConjecture.M14
