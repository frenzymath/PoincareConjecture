import PoincareConjecture.Proofs.M47.BlowupControlsCapRetained
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds

noncomputable local instance capTerminalCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capTerminalCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance capTerminalTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance capTerminalTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace

theorem cap_preterminal_retained_of_comparison_estimates
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} {A K0 K1 H Z k : ℝ}
    (hA : 0 < A) (hK0 : 0 < K0) (hK1 : 0 ≤ K1) (hZ : 0 < Z) (hk : 0 < k)
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    (O : SurgeryObservation F)
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    {start rNext deltaBar : ℝ}
    (hscales : SurgeryFixedScalesOn setup F O start rNext deltaBar)
    (hdelta : deltaBar ≤ M44.laterNeckRemovalCutoff.{u} hK0
      (M44.cylinderRemovalDiameter_pos g0 (K := K1) (H := H) hA hZ) hk)
    {origin h c : ℝ} {U V : Set (F.slice origin).carrier} (hh : 0 < h)
    (e : SurgeryFlowCylinder F (F.slice origin) origin (h⁻¹ ^ 2) (Ico 0 c) U)
    (survivor : SurgeryFlowCylinder F (F.slice origin) origin (h⁻¹ ^ 2) (Icc 0 c) V)
    (hc : 0 < c) (hcH : c ≤ H)
    (q : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace (F.slice origin).carrier ∞)
    (hsource : q.source = g0.metric.ball 0 A) (htarget : q.target = U)
    (G : M44.CylinderRicciFlow e q)
    (p : (⟨q.target, q.open_target⟩ : Opens (F.slice origin).carrier))
    (hscalar : ∀ s (hs : s ∈ Ico 0 c) x, x ∈ U → h ^ 2 *
      (F.connection (origin + s / (h⁻¹ ^ 2))).scalarCurvature (e.forward s hs x) ≤ K0)
    (hcurv : ∀ s ∈ Ico 0 c, ∀ y, (G.flow.connection s).curvatureTensorNorm y ≤ K1)
    (hbirth : ∀ x ∈ q.source,
      ‖(G.flow.metric 0).pullbackCoefficients (M44.targetChart q p) x‖ ≤ Z)
    {length : ℝ} {center : StandardCapSpace} (N : StandardCylinderPatch length center)
    (hball : ∀ z : UnitTwoSphere,
      M44.StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 A)
    (J : UnitTwoSphere → MetricTwoJet 3) {d s0 : ℝ} (hs0 : s0 < c)
    (hmargin : ∀ z J', ‖J' - J z‖ ≤ d →
      (z, J') ∈ M44.sphereSectionalJetRegion (M44.StandardCylinderPatch.sphereMap N) k)
    (hnear : ∀ s ∈ Ico 0 c, s0 ≤ s → ∀ z : UnitTwoSphere,
      ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (M44.targetChart q p))
        (M44.StandardCylinderPatch.sphereMap N z) - J z‖ ≤ d)
    (hT : origin + c / (h⁻¹ ^ 2) ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / (h⁻¹ ^ 2))).carrier]
    (htime : origin + c / (h⁻¹ ^ 2) ∈ surgeryObservationInterval O ∩ Ici start)
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / (h⁻¹ ^ 2) ∈
      Ico (F.event (origin + c / (h⁻¹ ^ 2)) hT).tMinus (origin + c / (h⁻¹ ^ 2)))
    (based : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
    (basedSurvivor : ∀ hs x, x ∈ V → HEq (survivor.forward 0 hs x) x)
    (y : (F.slice origin).carrier) (hyU : y ∈ U) (hyV : y ∈ V) :
    ∀ x ∈ U, ((F.event (origin + c / (h⁻¹ ^ 2)) hT).pre_identify
      ⟨origin + r / (h⁻¹ ^ 2), hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event (origin + c / (h⁻¹ ^ 2)) hT).retained_pre := by
  have hU : IsOpen U := htarget ▸ q.open_target
  have hconnected : IsPreconnected U := by
    have hpre : IsPreconnected q.source := hsource.symm ▸ g0.metric.isPreconnected_ball 0 A
    have himage := hpre.image q q.contMDiffOn.continuousOn
    rwa [q.toPartialEquiv.image_source_eq_target, htarget] at himage
  have hphysical (s : ℝ) (hs : s ∈ Ico 0 c) (x) (hx : x ∈ U) :
      (F.connection (origin + s / (h⁻¹ ^ 2))).scalarCurvature (e.forward s hs x) ≤ K0 / h ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
    simpa only [mul_comm] using hscalar s hs x hx
  have hline : ∀ x ∈ U, ∃ K : ℝ, ∀ s (hs : s ∈ Ico 0 c),
      (F.connection (origin + s / (h⁻¹ ^ 2))).scalarCurvature (e.forward s hs x) ≤ K :=
    fun x hx => ⟨K0 / h ^ 2, fun s hs => hphysical s hs x hx⟩
  apply cap_preterminal_retained_of_terminal_geometry P hpinch hK0
    (M44.cylinderRemovalDiameter_pos g0 (K := K1) (H := H) hA hZ) hk O setup hscales hdelta
    e survivor hc hU hconnected hT htime r hr hr' based basedSurvivor y hyU hyV g0 hA hh
    (M44.StandardCylinderPatch.sphereInBall N g0 A hball)
    (M44.terminalBirthBallTransport P hpinch e hU hT r hr hr' q hsource htarget hline)
    (M44.terminalBirthBallTransport_range P hpinch e hU hT r hr hr' q hsource htarget hline)
  · intro x
    change (F.event (origin + c / (h⁻¹ ^ 2)) hT).limit_connection.scalarCurvature
      (M44.cylinderTerminalChart e hU hT r hr hr' (q x)) ≤ K0 / h ^ 2
    exact M44.cylinderTerminalChart_scalar_le P hpinch e hU hT r hr hr'
      (htarget ▸ q.map_source (hsource.symm ▸ x.property))
      (fun s hs => hphysical s hs (q x) (htarget ▸ q.map_source (hsource.symm ▸ x.property)))
  · exact M44.terminalBirthBallTransport_diameter P hpinch e hU hT r hr hr'
      q hA hsource htarget hline G p hK1 hcH hZ hh rfl hcurv hbirth
  · exact M44.terminalBirthBallTransport_sphere_smooth P hpinch e hU hT r hr hr'
      q hsource htarget hline N hball
  · exact M44.terminalBirthBallTransport_sphere_immersion P hpinch e hU hT r hr hr'
      q hsource htarget hline N hball
  · intro z u v
    simpa only [div_eq_mul_inv, inv_pow] using
      M44.terminalBirthBallTransport_sphere_sectional P hpinch e hU hT r hr hr'
        q hA hsource htarget hline G p N hball J hs0 hmargin hnear z u v

end PoincareConjecture.M47
