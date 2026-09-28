import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalTransport
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_ChartDiameter
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalCylinderJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_PhysicalSphereMargin










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal ContinuousMap

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance terminalBallCoefficientNorm : NormedAddCommGroup
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance terminalBallCoefficientSpace : NormedSpace ℝ
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance terminalBallTwoJetNorm : NormedAddCommGroup
    (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance terminalBallTwoJetSpace : NormedSpace ℝ
    (MetricTwoJet 3) := Prod.normedSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c : ℝ} {U : Set C.carrier}

variable (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
  (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
  (hT : origin + c / scale ∈ F.surgery_times)
  [Nonempty (F.slice (origin + c / scale)).carrier]
  (r : ℝ) (hr : r ∈ Ico 0 c)
  (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
    (origin + c / scale))
  (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞)
  {g0 : StandardInitialMetric} {R : ℝ} (hR : 0 < R)
  (hsource : f.source = g0.metric.ball 0 R) (htarget : f.target = U)
  (hscalar : ∀ x ∈ U, ∃ K : ℝ, ∀ s (hs : s ∈ Ico (0 : ℝ) c),
    (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K)
  (G : CylinderRicciFlow e f)
  (p : (⟨f.target, f.open_target⟩ : Opens C.carrier))

include P hpinch hR hsource htarget hscalar



theorem terminalBirthBallTransport_diameter
    {K H Z h : ℝ} (hK : 0 ≤ K) (hcH : c ≤ H) (hZ : 0 < Z) (hh : 0 < h)
    (hscale : scale = h⁻¹ ^ 2)
    (hcurv : ∀ s ∈ Ico (0 : ℝ) c, ∀ y, (G.flow.connection s).curvatureTensorNorm y ≤ K)
    (hbirth : ∀ x ∈ f.source,
      ‖(G.flow.metric 0).pullbackCoefficients (targetChart f p) x‖ ≤ Z)
    (x y : g0.metric.ball 0 R) :
    (F.event (origin + c / scale) hT).limit_metric.edist
      (terminalBirthBallTransport P hpinch e hU hT r hr hr' f hsource htarget hscalar x)
      (terminalBirthBallTransport P hpinch e hU hT r hr hr' f hsource htarget hscalar y) <
        ENNReal.ofReal (h * (2 * Real.sqrt (Real.exp (6 * K * H) * Z) *
          M36.radialEuclideanRadius g0 R)) := by
  let B := Real.exp (6 * K * H) * Z
  have hB : 0 < B := mul_pos (Real.exp_pos _) hZ
  apply standard_ball_image_diameter_lt g0 _ hR hh (Real.sqrt_pos.mpr hB)
    (terminal_birth_chart_contMDiffOn P hpinch e hU hT r hr hr'
      f hsource htarget hscalar) _ x.property y.property
  intro z hz v
  have hzf : z ∈ f.source := hsource.symm ▸ hz
  have hinit : (G.flow.metric 0).pullbackCoefficients (targetChart f p) z v v ≤
      Z * ‖v‖ ^ 2 := by
    calc
      _ ≤ |(G.flow.metric 0).pullbackCoefficients (targetChart f p) z v v| := le_abs_self _
      _ ≤ ‖(G.flow.metric 0).pullbackCoefficients (targetChart f p) z‖ * ‖v‖ * ‖v‖ :=
        ((G.flow.metric 0).pullbackCoefficients (targetChart f p) z).le_opNorm₂ v v
      _ ≤ Z * ‖v‖ ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right (hbirth z hzf) (sq_nonneg ‖v‖)]
  have hbound (s : ℝ) (hs : s ∈ Ico (0 : ℝ) c) :
      (G.flow.metric s).pullbackCoefficients (targetChart f p) z v v ≤ B * ‖v‖ ^ 2 := by
    calc
      _ ≤ Real.exp (6 * K * c) *
          (G.flow.metric 0).pullbackCoefficients (targetChart f p) z v v :=
        G.pullback_quadratic_le_initial P hK hcurv p hs z v
      _ ≤ Real.exp (6 * K * c) * (Z * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le
      _ ≤ Real.exp (6 * K * H) * (Z * ‖v‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hZ.le (sq_nonneg _))
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcH (by positivity))
      _ = _ := by dsimp [B]; ring
  have hterminal := cylinderTerminalChart_quadratic_le P hpinch e hU hT r hr hr'
    f (le_of_eq htarget) G p hscalar hzf v hbound
  apply hterminal.trans_eq
  rw [hscale, inv_pow, inv_inv, mul_pow, Real.sq_sqrt hB.le]
  ring




theorem terminalBirthBallTransport_sphere_sectional
    {length : ℝ} {center : E} (N : StandardCylinderPatch length center)
    (hball : ∀ z : UnitTwoSphere,
      StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 R)
    (J : UnitTwoSphere → MetricTwoJet 3) {d k s0 : ℝ} (hs0 : s0 < c)
    (hmargin : ∀ z J', ‖J' - J z‖ ≤ d →
      (z, J') ∈ sphereSectionalJetRegion (StandardCylinderPatch.sphereMap N) k)
    (hnear : ∀ s ∈ Ico (0 : ℝ) c, s0 ≤ s → ∀ z : UnitTwoSphere,
      ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p))
        (StandardCylinderPatch.sphereMap N z) - J z‖ ≤ d)
    (z : UnitTwoSphere) (u v : TangentSpace (𝓡 2) z) :
    let transport := terminalBirthBallTransport P hpinch e hU hT r hr hr'
      f hsource htarget hscalar
    let sphere := transport.comp (StandardCylinderPatch.sphereInBall N g0 R hball)
    let D := mfderiv (𝓡 2) (𝓡 3) sphere z
    0 < (F.event (origin + c / scale) hT).limit_metric.inner (sphere z) (D u) (D u) *
      (F.event (origin + c / scale) hT).limit_metric.inner (sphere z) (D v) (D v) -
        ((F.event (origin + c / scale) hT).limit_metric.inner (sphere z) (D u) (D v)) ^ 2 →
      k * scale < (F.event (origin + c / scale) hT).limit_connection.sectionalCurvature
        (sphere z) (D u) (D v) := by
  dsimp only
  intro hgram
  have hopen : IsOpen (g0.metric.ball 0 R) := by
    rw [M36.standard_ball_eq_euclidean g0 hR]
    exact Metric.isOpen_ball
  apply sectional_lower_of_normalized_pullback_sphereJetRegion
    (StandardCylinderPatch.contMDiff_sphere N) _ _ hopen
    (terminal_birth_chart_contMDiffOn P hpinch e hU hT r hr hr'
      f hsource htarget hscalar)
    (fun x hx => terminal_birth_chart_mfderiv_invertible P hpinch e hU hT r hr hr'
      f hsource htarget hscalar hx) e.scale_pos (hball z) _ u v hgram
  apply hmargin
  exact cylinderTerminalChart_twoJet_near_of_tail P hpinch e hU hT r hr hr'
    f (le_of_eq htarget) G p hscalar (hsource.symm ▸ hball z) (J z) hs0
      (fun s hs htail => hnear s hs htail z)

end PoincareConjecture.M44
