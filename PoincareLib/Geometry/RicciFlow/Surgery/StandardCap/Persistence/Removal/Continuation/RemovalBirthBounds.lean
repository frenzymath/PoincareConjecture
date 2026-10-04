import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Normalization
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Initial.InitialComparisonBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Cylinder.CylinderBirthMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Initial.PhysicalBirthChart

/-!
# Birth coefficient bounds for the actual removal cylinder

The literal birth identity reads the normalized cylinder metric as
the actual M36 comparison coefficients on the whole birth chart.
Morgan--Tian, Lemma 16.8 and Claim 16.10, pp. 372-375;
M44 derivation 90.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

local notation "E" => StandardCapSpace

noncomputable local instance removalBirthCoefficientNorm : NormedAddCommGroup
    (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance removalBirthCoefficientSpace : NormedSpace ℝ
    (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

/-- A zero-order bound on the actual M36 coefficients bounds the
normalized cylinder metric on its whole physical birth chart.
Source: Claim 16.10, pp. 374-375; M44 derivation 90. -/
theorem cylinder_birth_coefficient_bound
    (F : SurgeryFlowData.{u}) (a : ℝ) (ha : a ∈ F.surgery_times)
    [Nonempty (F.slice a).carrier] (i : Fin (F.event a ha).cap_count)
    {eta B Z : ℝ} (hB : 0 < B)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event a ha).local_result i).output ((F.event a ha).local_result i).metric
      ((F.event a ha).local_result i).tip (((F.event a ha).necks i).neck.scale) eta)
    {U : Set (F.slice a).carrier}
    (e : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2) (Ico 0 B) U)
    (hinitial : ∀ h y, y ∈ U → HEq (e.forward 0 h y) y)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice a).carrier ∞)
    (hfU : f.target ⊆ U) (hfsource : f.source ⊆ F.standard_initial.metric.ball 0 eta⁻¹)
    (hfmap : ∀ y, f y = (F.event a ha).local_embed i (Q.map y))
    (G : CylinderRicciFlow e f)
    (p : (⟨f.target, f.open_target⟩ : Opens (F.slice a).carrier))
    (hQ : ∀ x ∈ f.source, ‖Q.normalizedCoefficients x‖ ≤ Z) :
    ∀ x ∈ f.source, ‖(G.flow.metric 0).pullbackCoefficients (targetChart f p) x‖ ≤ Z := by
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have hscale : 0 < (F.parameters.h a)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hh)
  let g := m01RescaledMetric (F.metric a) ((F.parameters.h a)⁻¹ ^ 2) hscale
  have hg (y) (v w) : g.inner y v w =
      (F.parameters.h a)⁻¹ ^ 2 * (F.metric a).inner y v w := rfl
  intro x hx
  rw [(G.initial_pullback_eq ⟨le_rfl, hB⟩ hfU hinitial g hg p hx).trans
    (physical_birth_pullback_eq F a ha i Q g hg f.open_source hfsource
      (fun y _ => hfmap y) hx)]
  exact hQ x hx

end PoincareMT.M44
