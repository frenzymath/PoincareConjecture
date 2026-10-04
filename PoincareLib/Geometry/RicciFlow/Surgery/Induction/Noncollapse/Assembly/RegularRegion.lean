import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.ConfigurationTransfer
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scales

/-!
# Actual tests, histories and minimizing regions

Morgan--Tian Proposition 16.4, p. 369, Proposition 16.5, p. 370,
and Remark 16.2, p. 368. These are local producer interfaces for the
actual regular history and its compact action sublevel.
-/

set_option autoImplicit false
-- Preserve the native and retained-slice tangent instances in these data.
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.Proofs.M46

/-- One actual closed-cylinder test from Definition 14.14 and Remark 16.2.
No compactness or analytic-history conclusion is assumed here. -/
structure NoncollapseTest (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) where
  time : ℝ
  time_mem : time ∈ surgeryObservationInterval O
  time_domain : time ∈ F.time_domain
  center : (F.slice time).carrier
  not_positive : ¬ SurgeryPositiveComponentAt F time center
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ F.parameters.epsilon
  cylinder : SurgeryFlowCylinder F (F.slice time) time 1
    (Icc (-radius ^ 2) 0) ((F.metric time).ball center radius)
  based : ∀ h y, y ∈ (F.metric time).ball center radius →
    HEq (cylinder.forward 0 h y) y
  curvature : ∀ s hs y, y ∈ (F.metric time).ball center radius →
    (F.connection (time + s / 1)).curvatureTensorNorm
      (cylinder.forward s hs y) ≤ radius⁻¹ ^ 2

/-- The included history associated to a test, Proposition 14.12, p. 350. -/
def NoncollapseTest.window {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (D : NoncollapseTest F O) : M33RegularHistoryWindow F :=
  F.closedRegularHistoryWindow D.time
    (D.cylinder.test_time_pos D.radius_pos) D.time_domain ⟨D.center⟩

/-- The history producer's literal target: the actual half-radius cylinder
and compact terminal closure needed by Theorem 8.1(2), p. 169. -/
structure HalfRadiusHistory {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (D : NoncollapseTest F O) where
  spacetime : M46RegularSpacetimeData D.window
  time_mem : D.time ∈ spacetime.history.generalized.interval
  center : (spacetime.history.generalized.slice D.time).carrier
  center_eq : spacetime.history.history.forward D.time time_mem center = D.center
  cylinder : GeneralizedFlowCylinder spacetime.history.generalized
    (spacetime.history.generalized.slice D.time) D.time 1
    (Icc (-(D.radius / 2) ^ 2) 0)
    ((spacetime.history.generalized.metric D.time).ball center (D.radius / 2))
  time_subset : Icc (D.time - (D.radius / 2) ^ 2) D.time ⊆
    spacetime.history.generalized.interval
  based : ∀ h y,
    y ∈ (spacetime.history.generalized.metric D.time).ball center (D.radius / 2) →
    cylinder.pointMap 0 h y = (⟨D.time, y⟩ : spacetime.history.generalized.point)
  curvature : ∀ s hs y,
    y ∈ (spacetime.history.generalized.metric D.time).ball center (D.radius / 2) →
    spacetime.history.generalized.curvatureNorm (cylinder.pointMap s hs y) ≤
      (D.radius / 2)⁻¹ ^ 2
  terminal_ball_compact : IsCompact (closure
    ((spacetime.geometry.toLGeometry.slices D.time).metricOnPoints.ball
      ((spacetime.geometry.sliceIdentification D.time).identification center)
      (D.radius / 2)))

/-- The compact path confinement supplied by the cap-action barriers and
Proposition 16.21, pp. 384-387. The strict action sublevel is explicit. -/
structure ActionConfinement {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport 3 X time I)
    (T start : ℝ) (x : G.Point) where
  barrier : ℝ
  barrier_large : 3 * Real.sqrt (T - start) < barrier
  cage : Set G.Point
  cage_compact : IsCompact cage
  paths_mem : ∀ tau : ℝ, 0 < tau → tau ≤ T - start → ∀ y : G.Point,
    ∀ path : M14BackwardPath G T 0 tau x y,
      M14BackwardLAction G path < barrier → MapsTo path.curve (Icc 0 tau) cage

/-- The regular minimizing region of Proposition 16.4, p. 369.
Openness is relative to the time strip, including its left endpoint. -/
structure MinimizingRegion {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport 3 X time I)
    (T start : ℝ) (x : G.Point) (confinement : ActionConfinement G T start x) where
  region : Set G.Point
  region_exact : ∀ y, y ∈ region ↔
    G.spacetime.timeFunction y ∈ Ico start T ∧
    ∃ path : M14BackwardPath G T 0 (T - G.spacetime.timeFunction y) x y,
      M14BackwardLAction G path < confinement.barrier
  time_mem : ∀ y ∈ region, G.spacetime.timeFunction y ∈ Ico start T
  relatively_open : ∃ U : Set G.Point, IsOpen U ∧
    region = U ∩ G.spacetime.timeFunction ⁻¹' Ico start T
  minimizing : ∀ y ∈ region,
    ∃ path : M14BackwardPath G T 0 (T - G.spacetime.timeFunction y) x y,
      M14IsMinimizing path
  slice_minimum : ∀ t ∈ Ico start T, ∃ y ∈ region,
    G.spacetime.timeFunction y = t ∧
    M14ActionValue G T 0 (T - t) x y ≤ 3 * Real.sqrt (T - t) ∧
    ∀ z ∈ region, G.spacetime.timeFunction z = t →
      M14ActionValue G T 0 (T - t) x y ≤ M14ActionValue G T 0 (T - t) x z
  compact_minima : ∀ a b : ℝ, Icc a b ⊆ Ico start T →
    IsCompact {y : G.Point | y ∈ region ∧ G.spacetime.timeFunction y ∈ Icc a b ∧
      ∀ z ∈ region, G.spacetime.timeFunction z = G.spacetime.timeFunction y →
        M14ActionValue G T 0 (T - G.spacetime.timeFunction y) x y ≤
          M14ActionValue G T 0 (T - G.spacetime.timeFunction y) x z}

/-- Positive-component propagation needed when applying the old guarded
volume seed along a backward path; Remark 16.2, p. 368. -/
def PositiveAncestorExclusion {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D) : Prop :=
  ∀ tau : ℝ, 0 < tau →
    ∀ ht : D.time - tau ∈ H.spacetime.history.generalized.interval,
    ∀ y : (H.spacetime.history.generalized.slice (D.time - tau)).carrier,
    Nonempty (M14BackwardPath H.spacetime.geometry.toLGeometry D.time 0 tau
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
      ((H.spacetime.geometry.sliceIdentification (D.time - tau)).identification y).val) →
    ¬ SurgeryPositiveComponentAt F (D.time - tau)
      (H.spacetime.history.history.forward (D.time - tau) ht y)

/-- M44's cap alternative on the actual overlap and the calibrated model.
The arbitrary observation is redecorated without changing its horizon.
Source: Proposition 16.5, p. 370. -/
def OverlapCapControl {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (old : SurgeryPrefixControls p F O) (A eta theta : ℝ) : Prop :=
  ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
    t ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ t →
    ∀ j : Fin (F.event t hT).cap_count,
      SurgeryCapPersistenceAlternative F (O.redecorateTo old.standard_initial_eq)
        t hT j A eta theta

end PoincareMT.Proofs.M46
