import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Continuation.RemovalAssembly
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Continuation.RemovalScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Terminal.TerminalBallGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.Stopping.MaximalCylinderStopping
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Initial.InitialChartBounds

/-!
# Whole-ball removal at an actual maximal cylinder endpoint

The normalized curvature and birth coefficients control terminal
diameter and scalar curvature. A preserved two-jet sphere margin
then excludes every later central neck. Maximality supplies the
actual surgery and lost line, including the empty-slice case.
Morgan--Tian, Claim 16.10, pp. 374-375; M44 derivation 79.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The closed sphere margin retains the nested coefficient slots.
set_option maxSynthPendingDepth 16

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal ContinuousMap

universe u

namespace PoincareMT.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance removalCylinderCoefficientNorm : NormedAddCommGroup
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance removalCylinderCoefficientSpace : NormedSpace ℝ
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance removalCylinderTwoJetNorm : NormedAddCommGroup
    (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance removalCylinderTwoJetSpace : NormedSpace ℝ
    (MetricTwoJet 3) := Prod.normedSpace

/-- The normalized diameter constant depends only on the model birth
ball, curvature bound, time bound and birth coefficients. Source:
Claim 16.10, p. 375; M44 derivation 79. -/
noncomputable def cylinderRemovalDiameter
    (g0 : StandardInitialMetric) (R K H Z : ℝ) : ℝ :=
  2 * Real.sqrt (Real.exp (6 * K * H) * Z) * M36.radialEuclideanRadius g0 R

/-- The diameter constant is positive for a positive birth radius
and coefficient bound. Source: Claim 16.10; M44 derivation 79. -/
theorem cylinderRemovalDiameter_pos
    (g0 : StandardInitialMetric) {R K H Z : ℝ} (hR : 0 < R) (hZ : 0 < Z) :
    0 < cylinderRemovalDiameter g0 R K H Z := by
  have hrho := (M36.radialEuclideanRadius_pos_iff g0 R).mpr hR
  have hsqrt := Real.sqrt_pos.mpr (mul_pos (Real.exp_pos (6 * K * H)) hZ)
  exact mul_pos (mul_pos (by norm_num) hsqrt) hrho

/-- The later-neck cutoff is selected before the physical flow and
birth height, with scalar constant `9 * K`. Source: Claim 16.10,
pp. 374-375; M44 derivation 79. -/
noncomputable def cylinderRemovalCutoff
    (g0 : StandardInitialMetric) {R K H Z k : ℝ}
    (hR : 0 < R) (hK : 0 < K) (hZ : 0 < Z) (hk : 0 < k) : ℝ :=
  laterNeckRemovalCutoff.{u} (mul_pos (by norm_num : (0 : ℝ) < 9) hK)
    (cylinderRemovalDiameter_pos g0 (K := K) (H := H) hR hZ) hk

/-- The uniform maximal-cylinder removal cutoff is positive.
Source: Claim 16.10, pp. 374-375; M44 derivation 79. -/
theorem cylinderRemovalCutoff_pos
    (g0 : StandardInitialMetric) {R K H Z k : ℝ}
    (hR : 0 < R) (hK : 0 < K) (hZ : 0 < Z) (hk : 0 < k) :
    0 < cylinderRemovalCutoff.{u} g0 (H := H) hR hK hZ hk :=
  laterNeckRemovalCutoff_pos.{u} (mul_pos (by norm_num : (0 : ℝ) < 9) hK)
    (cylinderRemovalDiameter_pos g0 (K := K) (H := H) hR hZ) hk

/-- An early maximal-cylinder endpoint is an actual surgery removing
the whole birth ball. All terminal geometric estimates, neck avoidance
and the fixed lost line are derived from the cylinder data. Source:
Claim 16.10, pp. 374-375; M44 derivation 79. -/
theorem maximal_cylinder_removal_of_bounds
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} {R K H Z k : ℝ}
    (hR : 0 < R) (hK : 0 < K) (hZ : 0 < Z) (hk : 0 < k)
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    (O : SurgeryObservation F)
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    {start rNext deltaBar : ℝ}
    (hscales : SurgeryFixedScalesOn setup F O start rNext deltaBar)
    (hdelta : deltaBar ≤ cylinderRemovalCutoff.{u} g0 (H := H) hR hK hZ hk)
    {origin h c B : ℝ} {U : Set (F.slice origin).carrier} (hh : 0 < h)
    (e : SurgeryFlowCylinder F (F.slice origin) origin (h⁻¹ ^ 2) (Ico 0 c) U)
    (hc : 0 < c) (hcB : c < B) (hcH : c ≤ H)
    (hclock : ∀ s ∈ Ico 0 B,
      origin + s / (h⁻¹ ^ 2) ∈ surgeryObservationInterval O ∩ Ici start)
    (hinitial : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
    (hstop : ∀ d : ℝ, c < d → d ≤ B →
      ¬ ∃ e' : SurgeryFlowCylinder F (F.slice origin) origin (h⁻¹ ^ 2) (Ico 0 d) U,
        ∀ hs x, x ∈ U → HEq (e'.forward 0 hs x) x)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice origin).carrier ∞)
    (hsource : f.source = g0.metric.ball 0 R) (htarget : f.target = U)
    (G : CylinderRicciFlow e f)
    (p : (⟨f.target, f.open_target⟩ : Opens (F.slice origin).carrier))
    (hcurv : ∀ s ∈ Ico (0 : ℝ) c, ∀ y, (G.flow.connection s).curvatureTensorNorm y ≤ K)
    (hbirth : ∀ x ∈ f.source,
      ‖(G.flow.metric 0).pullbackCoefficients (targetChart f p) x‖ ≤ Z)
    {length : ℝ} {center : E} (N : StandardCylinderPatch length center)
    (hball : ∀ z : UnitTwoSphere,
      StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 R)
    (J : UnitTwoSphere → MetricTwoJet 3) {d s0 : ℝ} (hs0 : s0 < c)
    (hmargin : ∀ z J', ‖J' - J z‖ ≤ d →
      (z, J') ∈ sphereSectionalJetRegion (StandardCylinderPatch.sphereMap N) k)
    (hnear : ∀ s ∈ Ico (0 : ℝ) c, s0 ≤ s → ∀ z : UnitTwoSphere,
      ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p))
        (StandardCylinderPatch.sphereMap N z) - J z‖ ≤ d) :
    origin + c / (h⁻¹ ^ 2) ∈ F.surgery_times ∧
      SurgeryBallDisappearsAt F e (origin + c / (h⁻¹ ^ 2)) := by
  classical
  have hU : IsOpen U := htarget ▸ f.open_target
  have htime : ∀ s ∈ Ico 0 B, origin + s / (h⁻¹ ^ 2) ∈ F.time_domain :=
    fun s hs => O.interval_subset (hclock s hs).1
  have hT := maximal_cylinder_endpoint_is_surgery e hU hc hcB htime hinitial hstop
  refine ⟨hT, ?_⟩
  by_cases hn : Nonempty (F.slice (origin + c / (h⁻¹ ^ 2))).carrier
  · let := hn
    have hconnected : IsPreconnected U := by
      have hpre : IsPreconnected f.source :=
        hsource.symm ▸ g0.metric.isPreconnected_ball 0 R
      have himage := hpre.image f f.contMDiffOn.continuousOn
      rw [f.toPartialEquiv.image_source_eq_target, htarget] at himage
      exact himage
    have hscalarNormalized (s : ℝ) (hs : s ∈ Ico (0 : ℝ) c) (y) :
        (G.flow.connection s).scalarCurvature y ≤ 9 * K := by
      calc
        _ ≤ |(G.flow.connection s).scalarCurvature y| := le_abs_self _
        _ ≤ 9 * (G.flow.connection s).curvatureTensorNorm y := by
          have hb := abs_scalar_le_curvatureTensorNorm (G.flow.connection s) y
          norm_num at hb
          exact hb
        _ ≤ 9 * K := mul_le_mul_of_nonneg_left (hcurv s hs y) (by norm_num)
    have hscalar (s : ℝ) (hs : s ∈ Ico (0 : ℝ) c) (x) (hx : x ∈ U) :
        (F.connection (origin + s / (h⁻¹ ^ 2))).scalarCurvature (e.forward s hs x) ≤
          (9 * K) / h ^ 2 :=
      G.physical_scalar_le_height hU htarget hs (hscalarNormalized s hs) hx
    have hline : ∀ x ∈ U, ∃ L : ℝ, ∀ s (hs : s ∈ Ico (0 : ℝ) c),
        (F.connection (origin + s / (h⁻¹ ^ 2))).scalarCurvature (e.forward s hs x) ≤ L :=
      fun x hx => ⟨(9 * K) / h ^ 2, fun s hs => hscalar s hs x hx⟩
    obtain ⟨r, hr, hr'⟩ := exists_preterminal_parameter e.scale_pos hc
      (F.event (origin + c / (h⁻¹ ^ 2)) hT).tMinus_lt
    have hlost := maximal_cylinder_has_fixed_lost_line P hpinch e hU hc hcB
      htime hinitial hstop hT
    apply disappears_of_terminal_geometry P
      (mul_pos (by norm_num : (0 : ℝ) < 9) hK)
      (cylinderRemovalDiameter_pos g0 (K := K) (H := H) hR hZ) hk
      hpinch O setup hscales hdelta e hU hconnected hT (hclock c ⟨hc.le, hcB⟩)
      r hr hr' hinitial hlost g0 hR hh
      (StandardCylinderPatch.sphereInBall N g0 R hball)
      (terminalBirthBallTransport P hpinch e hU hT r hr hr' f hsource htarget hline)
      (terminalBirthBallTransport_range P hpinch e hU hT r hr hr'
        f hsource htarget hline) hscalar
    · exact terminalBirthBallTransport_diameter P hpinch e hU hT r hr hr'
        f hR hsource htarget hline G p hK.le hcH hZ hh rfl hcurv hbirth
    · exact terminalBirthBallTransport_sphere_smooth P hpinch e hU hT r hr hr'
        f hsource htarget hline N hball
    · exact terminalBirthBallTransport_sphere_immersion P hpinch e hU hT r hr hr'
        f hsource htarget hline N hball
    · intro z u v
      simpa only [div_eq_mul_inv, inv_pow] using
        terminalBirthBallTransport_sphere_sectional P hpinch e hU hT r hr hr'
          f hR hsource htarget hline G p N hball J hs0 hmargin hnear z u v
  · exact Or.inl ⟨fun x => hn ⟨x⟩⟩

end PoincareMT.M44
