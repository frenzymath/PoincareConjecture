import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicShapeAmbientBall
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicCenterNormalization
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicCollarPoint
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicCollarJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => StandardCapSpace

theorem blowupSequence_intrinsic_collar_profile_jets
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
    ∀ (_N : M27SphereLineFlowCertificate A.solution),
      ∀ (idx : ℕ → ℕ), Tendsto idx atTop atTop →
      let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence (idx k))
      let hQ k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence (idx k))
      let G (k : ℕ) : RiemannianMetric 3 V :=
        M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence (idx k)))) (Q k) (hQ k)
      let hrot k := scaleSmoothMetric_rotation_invariant
        (E.rotation_invariant (t (L.subsequence (idx k))) (ht _)) (Q k) (hQ k)
      let hc k := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence (idx k))))
        (E.complete (t (L.subsequence (idx k))) (ht _)) (Q k) (hQ k)
      let a k := radialArclength (G k) ‖x (L.subsequence (idx k))‖
      ∀ (s : ℕ → ℝ) (length : ℝ), 0 ≤ length →
        (∀ᶠ k in atTop, |s k - a k| ≤ length) → ∀ m : ℕ,
        Tendsto (fun k => iteratedDeriv m
          (fun u => intrinsicWarpingRadius (G k) (hrot k) (hc k) u ^ 2) (s k))
          atTop (𝓝 (if m = 0 then 2 else 0)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N idx hidx
  dsimp only
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence (idx k))
  have hQ (k : ℕ) : 0 < Q k :=
    (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence (idx k))
  let G (k : ℕ) : RiemannianMetric 3 V :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence (idx k)))) (Q k) (hQ k)
  have hrot k := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t (L.subsequence (idx k))) (ht _)) (Q k) (hQ k)
  have hc k := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence (idx k))))
    (E.complete (t (L.subsequence (idx k))) (ht _)) (Q k) (hQ k)
  let D k := M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence (idx k))))
    (Q k) (hQ k)
  have hsec k : (D k).NonnegativeSectionalCurvature :=
    scaleLeviCivitaData_nonnegative_sectional
      (E.flow.connection (t (L.subsequence (idx k))))
      (E.nonnegative_sectional (t (L.subsequence (idx k))) (ht _)) (Q k) (hQ k)
  let a k := radialArclength (G k) ‖x (L.subsequence (idx k))‖
  obtain ⟨ha₀, hcenter₀⟩ := blowupSequence_intrinsic_center_limits P E t x ht hR hd L
  have ha : Tendsto a atTop atTop := ha₀.comp hidx
  have hcenter := hcenter₀.comp hidx
  intro s length hlength hcollar
  have hs : ∀ᶠ k in atTop, 0 < s k := by
    filter_upwards [ha.eventually (eventually_gt_atTop (length + 1)), hcollar]
      with k hak hsk
    linarith [(abs_le.mp hsk).1]
  have hvalue := intrinsic_collar_orbit_sq_tendsto_two G hrot hc D hsec a s ha hcenter
    hlength hcollar
  apply intrinsic_orbit_sq_jets_tendsto G hrot hc s hs hvalue
  intro m
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hball := hidx.eventually (blowupSequence_intrinsic_shape_on_ambient_ball
    P E t x ht hR hd L A N m (length + 1) epsilon (by positivity) hepsilon)
  filter_upwards [hs, hcollar, hball] with k hsk hck hbk
  obtain ⟨y, hys, hyd⟩ := exists_intrinsic_collar_point (G k) (hrot k) (hc k)
    P (x (L.subsequence (idx k))) hsk
  have hymem : y ∈ (G k).ball (x (L.subsequence (idx k))) (length + 1) := by
    exact hyd.trans_lt ((ENNReal.ofReal_le_ofReal hck).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity : (0 : ℝ) < length + 1)).mpr
        (by linarith)))
  have hh := hbk y hymem
  rw [hys] at hh
  simpa only [Real.dist_eq, sub_zero] using hh

end PoincareConjecture.M35.OrdinaryRealization
