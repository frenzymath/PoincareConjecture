import PoincareConjecture.Proofs.M35.CapGeometry.SelectedRadialFieldParallel
import PoincareConjecture.Proofs.M35.CapGeometry.ReflectedPullbackComposition
import PoincareConjecture.Proofs.M35.CapGeometry.ReflectedChartPair
import PoincareConjecture.Proofs.M35.CapGeometry.FarTipModelAlternatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_far_tip_not_twisted
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
    ¬Nonempty (M27TwistedSphereLineFlowCertificate A.solution) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  rintro ⟨N⟩
  obtain ⟨q, a, b, R, _hRpos, ha, hb, hab⟩ := exists_reflected_pair_in_chart_ball
  let coordinate := N.cover ∘ cylinderChart q
  let g := twistedProductChartMetric N 0 q
  let D := twistedProductChartConnection N 0 q
  have hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate := twistedProductChart_contMDiff N q
  have hi : ∀ z, (mfderiv (𝓡 3) (𝓡 3) coordinate z).IsInvertible :=
    twistedProductChart_invertible N q
  have hg : g.euclideanCoefficients = (L.limit.flow.metric 0).pullbackCoefficients coordinate := by
    change (A.solution.flow.metric 0).pullbackCoefficients coordinate = _
    rw [A.metric_eq 0 le_rfl]
  let Ω : Set V := Metric.ball 0 R
  have hΩ : IsOpen Ω := Metric.isOpen_ball
  have hcompact : IsCompact (closure Ω) :=
    (isCompact_closedBall (0 : V) R).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  obtain ⟨sigma, Z, hsigma, hZ, hjets⟩ :=
    blowupSequence_coordinate_radial_smooth_subsequence P E t x ht hR hd L
      coordinate hc hi g hg Ω hΩ hcompact
  have hpointJets (m : ℕ) (z : V) (hz : z ∈ Ω) :=
    (hjets m {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at (mem_singleton z)
  have hparallel (z : V) (hz : z ∈ Ω) :
      g.inner z (Z z) (Z z) = 1 ∧ ∀ w : V, D.connection Z z w = 0 :=
    blowupSequence_coordinate_radial_limit_parallel P E t x ht hR hd L
      coordinate hc hi g D hg sigma hsigma.tendsto_atTop z Z
      ((hZ z hz).contDiffAt (hΩ.mem_nhds hz)) (fun m _ => hpointJets m z hz)
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
  have hQ k : 0 < Q k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence (sigma k))
  let G (k : ℕ) : RiemannianMetric 3 StandardCapSpace :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence (sigma k)))) (Q k) (hQ k)
  let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) := ((L.embedding (sigma k)).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ z).val
  let W (k : ℕ) := mpullback (𝓡 3) (𝓡 3) (F k) (radialUnitField (G k))
  have hvalue (z : V) (hz : z ∈ Ω) :
      Tendsto (fun k => twistedChartLift N q (W k) z) atTop (𝓝 (Z z)) := by
    have hval := ((continuousMultilinearCurryFin0 ℝ V V).continuous.tendsto _).comp
      (hpointJets 0 z hz)
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] at hval
    have hcover : coordinate z ∈ ⋃ j, L.exhaustion.space j := by
      rw [L.exhaustion.space_covers]
      exact mem_univ _
    obtain ⟨j, hzj⟩ := mem_iUnion.mp hcover
    apply hval.congr'
    filter_upwards [hsigma.tendsto_atTop.eventually (eventually_ge_atTop j)] with k hk
    have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time (sigma k)) 0 :=
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
    have htime := ((L.embedding (sigma k)).forward 0 hzero L.limit.base).property
    have hF : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (F k) (coordinate z) :=
      ((sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
        ((L.embedding (sigma k)).forward_smooth 0 hzero)).contMDiffAt
          ((L.exhaustion.space_open (sigma k)).mem_nhds
            (L.exhaustion.space_increasing hk hzj))
    exact (twistedChartLift_mpullback_comp N q (F k) (radialUnitField (G k)) z
      (hF.mdifferentiableAt (by simp))).symm
  exact twistedChartLift_parallel_limit_false N q W hΩ (convex_ball (0 : V) R).isPreconnected
    hZ (fun z hz => (hparallel z hz).2) ha hb (hparallel a ha).1 hab
    (hvalue a ha) (hvalue b hb)

theorem blowupSequence_far_tip_sphere_line
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
    ∀ {epsilon C : ℝ}, M27KappaNine93Conclusion A.solution epsilon C →
      Nonempty (M27SphereLineFlowCertificate A.solution) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro epsilon C H
  exact (blowupSequence_far_tip_product_models P E t x ht hR hd L A H).resolve_right
    (blowupSequence_far_tip_not_twisted P E t x ht hR hd L A)

end PoincareConjecture.M35.OrdinaryRealization
