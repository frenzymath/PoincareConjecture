import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Compactness.CylinderCompactnessFeedData
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.InitialCylinder
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.Stopping.MaximalCylinder

/-!
# Actual maximal-cylinder samples

An exact M36 birth comparison supplies an actual compactness sample
on its maximal physical cylinder, preserving the chosen comparison
map when the radius changes. Morgan--Tian, Proposition 16.5 and
Claim 16.6, pp. 371-374; M44 derivation 100.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M44

/-- An actual sample on the maximal cylinder of its physical birth
ball below the assigned duration. Source: Proposition 16.5, p. 374;
M44 derivation 100. -/
structure MaximalCapSample (g0 : StandardInitialMetric)
    (F : SurgeryFlowData.{u}) (a : ℝ) (ha : a ∈ F.surgery_times)
    [Nonempty (F.slice a).carrier] (i : Fin (F.event a ha).cap_count) (B : ℝ)
    extends CylinderCompactnessSample g0 F a ha i where
  /-- The chart covers precisely the tracked region. -/
  target_eq : chart.target = region
  /-- The tracked region is the actual physical birth ball. -/
  region_eq : region =
    (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * radius)
  /-- The maximal cylinder remains below its assigned duration. -/
  lifetime_le : lifetime ≤ B
  /-- No based cylinder on this ball extends past its lifetime below B. -/
  maximal : ∀ d : ℝ, lifetime < d → d ≤ B →
    ¬ ∃ e : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2)
      (Ico 0 d) region, ∀ hs x, x ∈ region → HEq (e.forward 0 hs x) x

namespace MaximalCapSample

variable {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a B : ℝ}
  {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
  {i : Fin (F.event a ha).cap_count}

/-- The actual maximal sample tracks an open region. Source:
Proposition 16.5, p. 374; M44 derivation 100. -/
theorem region_open (D : MaximalCapSample g0 F a ha i B) : IsOpen D.region :=
  D.target_eq ▸ D.chart.open_target

/-- The actual maximal sample tracks a nonempty ball. Source:
Proposition 16.5, p. 374; M44 derivation 100. -/
theorem region_nonempty (D : MaximalCapSample g0 F a ha i B) : D.region.Nonempty := by
  rw [← D.target_eq]
  exact ⟨D.target_point.1, D.target_point.2⟩

end MaximalCapSample

/-- Every supplied exact M36 comparison gives a maximal sample on
any strictly buffered positive radius, without changing its comparison
map. Source: Proposition 16.5 and Claim 16.6, pp. 371-374;
M44 derivation 100. -/
theorem exists_maximal_cap_sample
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (F : SurgeryFlowData.{u})
    (a : ℝ) (ha : a ∈ F.surgery_times) [Nonempty (F.slice a).carrier]
    (i : Fin (F.event a ha).cap_count) (hg0 : F.standard_initial = g0)
    (hpinch : SurgeryFlowPinched F)
    {B R eta : ℝ} (hB : 0 < B) (hR : 0 < R) (hfit : R < eta⁻¹)
    (htime : ∀ s ∈ Ico 0 B,
      a + s / ((F.parameters.h a)⁻¹ ^ 2) ∈ F.time_domain)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event a ha).local_result i).output ((F.event a ha).local_result i).metric
      ((F.event a ha).local_result i).tip (((F.event a ha).necks i).neck.scale) eta)
    (hballs : ∀ r : ℝ, 0 < r → r ≤ eta⁻¹ →
      Q.map '' F.standard_initial.metric.ball 0 r =
        ((F.event a ha).local_result i).metric.ball ((F.event a ha).local_result i).tip
          (((F.event a ha).necks i).neck.scale * r)) :
    ∃ D : MaximalCapSample g0 F a ha i B,
      D.radius = R ∧ D.eta = eta ∧ D.comparison.map = Q.map := by
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have hscale : 0 < (F.parameters.h a)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hh)
  obtain ⟨chart, hsource, hmap, htarget, _hconnected⟩ :=
    exists_physical_birth_chart F a ha i hR hfit Q (hballs R hR hfit.le)
  let U := (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R)
  have hU : IsOpen U := by
    simpa only [U, ← htarget] using chart.open_target
  obtain ⟨b0, hb0, hb0B, e0, he0⟩ := exists_initial_based_cylinder F hscale hB htime U
  obtain ⟨c, hc, hcB, e, he, _hagree, hmax⟩ :=
    exists_maximal_based_cylinder e0 hb0 hb0B.le he0
  have hmapU : chart.target ⊆ U := htarget ▸ Subset.rfl
  obtain ⟨G⟩ := exists_cylinderRicciFlow P hpinch e hU hc chart hmapU
  have hzero : (0 : StandardCapSpace) ∈ chart.source := by
    rw [hsource, M36.standard_ball_eq_euclidean F.standard_initial hR]
    exact Metric.mem_ball_self
      ((M36.radialEuclideanRadius_pos_iff F.standard_initial R).mpr hR)
  let point : (⟨chart.target, chart.open_target⟩ : Opens (F.slice a).carrier) :=
    ⟨chart 0, chart.map_source hzero⟩
  let D : MaximalCapSample g0 F a ha i B :=
    { standard_initial_eq := hg0
      radius := R
      radius_pos := hR
      eta := eta
      radius_lt := hfit
      lifetime := c
      lifetime_pos := hc
      comparison := Q
      image_ball := hballs
      chart := chart
      chart_source := hsource
      chart_eq := hmap
      region := U
      cylinder := e
      chart_target_subset := hmapU
      birth_identity := he
      ordinary := G
      target_point := point
      target_eq := htarget
      region_eq := rfl
      lifetime_le := hcB
      maximal := hmax }
  exact ⟨D, rfl, rfl, rfl⟩

end PoincareMT.M44
