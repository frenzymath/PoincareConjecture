import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Normalization.Soul
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Based
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Geodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

section Transport

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
  (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (he : MetricHomothety g h e 1)

include he in

theorem MetricHomothety.symm_one : MetricHomothety h g e.symm 1 := by
  intro y v w
  have hcomp : e ∘ e.symm = id := by funext z; exact e.apply_symm_apply z
  have hd := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (e.symm y))
    (e.symm.contMDiff.mdifferentiable (by simp) y)
  rw [hcomp, mfderiv_id] at hd
  have hv (z : TangentSpace (𝓡 3) y) :
      mfderiv (𝓡 3) (𝓡 3) e (e.symm y)
        (mfderiv (𝓡 3) (𝓡 3) e.symm y z) = z :=
    (congrArg (fun A => A z) hd).symm
  have hm := he (e.symm y)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y v) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)
  rw [hv v, hv w, e.apply_symm_apply, one_mul] at hm
  simpa only [one_mul] using hm.symm

def RiemannianMetric.PointSoulData.mapIsometry (P : RiemannianMetric.PointSoulData g) :
    RiemannianMetric.PointSoulData h where
  center := e P.center
  totallyConvex_singleton := by
    intro curve a b hcurve ha hb
    change curve a = e P.center at ha
    change curve b = e P.center at hb
    have hi := MetricHomothety.symm_one e he
    have hcurve' := hcurve.comp_local_isometry_manifold isOpen_univ
      e.symm.contMDiff.contMDiffOn
      (fun x _ v w => by simpa only [one_mul] using (hi x v w).symm)
      (fun _ _ => mem_univ _)
    have ha' : (e.symm ∘ curve) a ∈ ({P.center} : Set M) := by
      simp only [Function.comp_apply, mem_singleton_iff, ha, e.symm_apply_apply]
    have hb' : (e.symm ∘ curve) b ∈ ({P.center} : Set M) := by
      simp only [Function.comp_apply, mem_singleton_iff, hb, e.symm_apply_apply]
    intro t ht
    have hp := P.totallyConvex_singleton (e.symm ∘ curve) a b hcurve' ha' hb' ht
    have hpt := congrArg e (show e.symm (curve t) = P.center from hp)
    simpa only [mem_singleton_iff, e.apply_symm_apply] using hpt
  euclidean := P.euclidean.trans e
  euclidean_zero := by
    change e (P.euclidean 0) = e P.center
    exact congrArg e P.euclidean_zero
  radial := {
    toHomeomorph := P.radial.toHomeomorph.trans
      (e.toHomeomorph.subtype (fun x => by
        change x ≠ P.center ↔ e x ≠ e P.center
        exact not_congr e.injective.eq_iff.symm))
    distance_eq := by
      intro z
      change (h.edist (e P.center) (e (P.radial.toHomeomorph z))).toReal = z.2.val
      rw [Homothety.homothety_edist g h e 1 zero_lt_one he,
        Real.sqrt_one, ENNReal.ofReal_one, one_mul]
      exact P.radial.distance_eq z }

@[simp] theorem RiemannianMetric.PointSoulData.mapIsometry_center
    (P : RiemannianMetric.PointSoulData g) :
    (P.mapIsometry e he).center = e P.center := rfl

theorem RiemannianMetric.PointSoulData.mapIsometry_edist
    (P : RiemannianMetric.PointSoulData g) (x : M) :
    h.edist (e x) (P.mapIsometry e he).center = g.edist x P.center := by
  simpa only [mapIsometry_center, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
    Homothety.homothety_edist g h e 1 zero_lt_one he x P.center

end Transport

namespace AncientKappaSolution

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  (K : AncientKappaSolution 3 M) (q : M) {kappa : ℝ}
  (hkappa : 0 < kappa) (hnoncollapsed : AncientKappaNoncollapsed K.flow kappa)
  (hnormalized : (K.flow.connection 0).scalarCurvature q = 1)

def pointSoulToSmallBased (P : RiemannianMetric.PointSoulData (K.flow.metric 0)) :
    RiemannianMetric.PointSoulData
      ((K.toSmallBased q hkappa hnoncollapsed hnormalized).flow.flow.metric 0) :=
  P.mapIsometry (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M)
    (K.flow.metricHomothety_shrink 0)

@[simp] theorem pointSoulToSmallBased_center
    (P : RiemannianMetric.PointSoulData (K.flow.metric 0)) :
    (K.pointSoulToSmallBased q hkappa hnoncollapsed hnormalized P).center =
      equivShrink M P.center := rfl

theorem pointSoulToSmallBased_edist
    (P : RiemannianMetric.PointSoulData (K.flow.metric 0)) :
    ((K.toSmallBased q hkappa hnoncollapsed hnormalized).flow.flow.metric 0).edist
      (K.toSmallBased q hkappa hnoncollapsed hnormalized).base
      (K.pointSoulToSmallBased q hkappa hnoncollapsed hnormalized P).center =
      (K.flow.metric 0).edist q P.center :=
  P.mapIsometry_edist (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M)
    (K.flow.metricHomothety_shrink 0) q

end AncientKappaSolution

end PoincareConjecture
