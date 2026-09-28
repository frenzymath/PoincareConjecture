import PoincareConjecture.Proofs.M35.CapGeometry.SelectedIntrinsicShapeCompact
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedAmbientBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_intrinsic_shape_on_ambient_ball
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ (_N : M27SphereLineFlowCertificate A.solution) (m : ℕ) (r epsilon : ℝ),
      0 < r → 0 < epsilon → ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      let G : RiemannianMetric 3 V :=
        M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
      let hrot := scaleSmoothMetric_rotation_invariant
        (E.rotation_invariant (t (L.subsequence k)) (ht _)) Q hQ
      let hc := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence k)))
        (E.complete (t (L.subsequence k)) (ht _)) Q hQ
      ∀ y ∈ G.ball (x (L.subsequence k)) r,
        |iteratedDeriv m (intrinsicRadialShape G hrot hc) (radialArclength G ‖y‖)| <
          epsilon := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N m r epsilon hr hepsilon
  let K : Set L.limit.sliceCarrier.carrier :=
    closure ((L.limit.flow.metric 0).ball L.limit.base (2 * r))
  have hK : IsCompact K := Proofs.M09.isCompact_closure_metric_ball
    (L.limit.flow.metric 0) (L.limit.complete 0 L.limit.zero_mem) L.limit.base (2 * r)
  have hshape := blowupSequence_intrinsic_shape_uniform_compact
    P E t x ht hR L hd A N K hK m epsilon hepsilon
  filter_upwards [hshape, blowupSequence_normalized_ball_retained P E t x ht hR L hr]
    with k hk hball
  dsimp only
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hball hy
  have h := hk z (subset_closure hz)
  unfold selectedIntrinsicShapeDerivative at h
  simpa only [hzy] using h

end PoincareConjecture.M35.OrdinaryRealization
