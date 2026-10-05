import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Normalization
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Cylinder.CylinderCoordinateEstimates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Compactness.CompactnessFeedJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.RicciTimeGluing

/-!
# The actual surgery-cylinder data used in compactness

Each sample retains its physical surgery cap, exact-ball birth comparison,
surviving cylinder, and normalized ordinary flow. Its coefficient field is
the actual pullback in the fixed birth chart. No limit or analytic estimate
is stored in this record. Morgan--Tian, Claim 16.6 and Lemma 16.8,
pp. 371-373; M44 derivation 88.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance cylinderFeedCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance cylinderFeedCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

/-- One actual normalized surgery-cylinder sample with its initial
M36 exact-ball chart. Source: Claim 16.6 and Lemma 16.8;
M44 derivation 88. -/
structure CylinderCompactnessSample (g0 : StandardInitialMetric)
    (F : SurgeryFlowData.{u}) (a : ℝ) (ha : a ∈ F.surgery_times)
    [Nonempty (F.slice a).carrier] (i : Fin (F.event a ha).cap_count) where
  /-- The fixed initial standard metric. -/
  standard_initial_eq : F.standard_initial = g0
  /-- The actual birth-chart radius. -/
  radius : ℝ
  /-- Its positive radius. -/
  radius_pos : 0 < radius
  /-- The actual comparison tolerance. -/
  eta : ℝ
  /-- The chart fits strictly inside the comparison domain. -/
  radius_lt : radius < eta⁻¹
  /-- The actual normalized survival duration. -/
  lifetime : ℝ
  /-- The surviving cylinder has a positive duration. -/
  lifetime_pos : 0 < lifetime
  /-- The certificate uses the actual local surgery result. -/
  comparison : SurgeryCapClose F.standard_initial
    ((F.event a ha).local_result i).output ((F.event a ha).local_result i).metric
    ((F.event a ha).local_result i).tip (((F.event a ha).necks i).neck.scale) eta
  /-- The corrected birth comparison preserves every included ball. -/
  image_ball : ∀ r : ℝ, 0 < r → r ≤ eta⁻¹ →
    comparison.map '' F.standard_initial.metric.ball 0 r =
      ((F.event a ha).local_result i).metric.ball ((F.event a ha).local_result i).tip
        (((F.event a ha).necks i).neck.scale * r)
  /-- The physical birth chart in the actual post-surgery slice. -/
  chart : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice a).carrier ∞
  /-- Its literal standard-coordinate domain. -/
  chart_source : chart.source = F.standard_initial.metric.ball 0 radius
  /-- The chart is the actual local surgery embedding. -/
  chart_eq : ∀ y, chart y = (F.event a ha).local_embed i (comparison.map y)
  /-- The actual tracked physical region. -/
  region : Set (F.slice a).carrier
  /-- Its surviving cylinder. -/
  cylinder : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2)
    (Ico 0 lifetime) region
  /-- The whole chart target is tracked. -/
  chart_target_subset : chart.target ⊆ region
  /-- The cylinder starts at the actual birth points. -/
  birth_identity : ∀ h y, y ∈ region → HEq (cylinder.forward 0 h y) y
  /-- The normalized Ricci flow on the physical chart target. -/
  ordinary : CylinderRicciFlow cylinder chart
  /-- A target point only totalizes the coordinate map off its source. -/
  target_point : (⟨chart.target, chart.open_target⟩ : Opens (F.slice a).carrier)

namespace CylinderCompactnessSample

variable {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a : ℝ}
  {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
  {i : Fin (F.event a ha).cap_count}

/-- The actual normalized coefficient family. Source: the fixed
birth charts in Lemma 16.8; M44 derivation 88. -/
noncomputable def coefficients (D : CylinderCompactnessSample g0 F a ha i) :
    ℝ × E → MetricCoefficient 3 := fun p =>
  (D.ordinary.flow.metric p.1).pullbackCoefficients (targetChart D.chart D.target_point) p.2

/-- The source uses the fixed standard initial metric. Source:
Corollary 16.7 and Lemma 16.8; M44 derivation 88. -/
theorem source_eq (D : CylinderCompactnessSample g0 F a ha i) :
    D.chart.source = g0.metric.ball 0 D.radius := by
  rw [D.chart_source, D.standard_initial_eq]

/-- The actual coefficient field is smooth on its full included
birth cylinder. Source: Lemma 16.8; M44 derivation 88. -/
theorem coefficients_smooth (D : CylinderCompactnessSample g0 F a ha i) :
    ContDiffOn ℝ ∞ D.coefficients (Ico 0 D.lifetime ×ˢ D.chart.source) :=
  contDiffOn_pullbackCoefficients_within D.ordinary.flow D.chart.open_source
    (contMDiffOn_targetChart D.chart D.target_point)

/-- The target-valued birth chart has invertible differential on
its actual source. Source: Claim 16.6; M44 derivation 88. -/
theorem target_derivative_invertible (D : CylinderCompactnessSample g0 F a ha i)
    {x : E} (hx : x ∈ D.chart.source) :
    (mfderiv (𝓡 3) (𝓡 3) (targetChart D.chart D.target_point) x).IsInvertible := by
  have h := (targetPartialDiffeomorph D.chart D.target_point).isLocalDiffeomorphAt
    (𝓡 3) (𝓡 3) ∞ hx
  exact ⟨h.mfderivToContinuousLinearEquiv (by simp), rfl⟩

/-- Positive actual metrics have invertible coordinate coefficients.
Source: Claim 16.6; M44 derivation 88. -/
theorem coefficients_invertible (D : CylinderCompactnessSample g0 F a ha i)
    (t : ℝ) {x : E} (hx : x ∈ D.chart.source) :
    (D.coefficients (t, x)).IsInvertible :=
  (D.ordinary.flow.metric t).isInvertible_pullbackCoefficients
    (D.target_derivative_invertible hx).injective

/-- Symmetry is inherited from the actual normalized metric at
every argument. Source: Claim 16.6; M44 derivation 88. -/
theorem coefficients_symmetric (D : CylinderCompactnessSample g0 F a ha i)
    (p : ℝ × E) (v w : E) : D.coefficients p v w = D.coefficients p w v :=
  (D.ordinary.flow.metric p.1).symm _ _ _

/-- Restriction to the actual open time interior gives the native
coordinate Ricci equation. Source: Lemma 16.8; derivation 88. -/
theorem coefficients_evolution (D : CylinderCompactnessSample g0 F a ha i)
    {t : ℝ} (ht : t ∈ Ioo 0 D.lifetime) {x : E} (hx : x ∈ D.chart.source) :
    HasDerivAt (fun s => D.coefficients (s, x))
      (ricciFlowOperator 3 (metricTwoJet (fun y => D.coefficients (t, y)) x)) t := by
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow D.ordinary.flow
    (show Ioo (0 : ℝ) D.lifetime ⊆ Ico 0 D.lifetime from Ioo_subset_Ico_self)
    ordConnected_Ioo (Ioo_infinite D.lifetime_pos).nontrivial
  exact hasDerivAt_pullbackCoefficients_ricci G isOpen_Ioo D.chart.open_source
    (contMDiffOn_targetChart D.chart D.target_point)
    (fun _ hy => D.target_derivative_invertible hy) ht hx

/-- At birth the actual normalized coefficient field equals the
M36 comparison field on the full open chart. Source: Corollary 16.7;
M44 derivation 88. -/
theorem initial_coefficients (D : CylinderCompactnessSample g0 F a ha i)
    {x : E} (hx : x ∈ D.chart.source) :
    D.coefficients (0, x) = D.comparison.normalizedCoefficients x := by
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have hscale : 0 < (F.parameters.h a)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hh)
  let g := m01RescaledMetric (F.metric a) ((F.parameters.h a)⁻¹ ^ 2) hscale
  have hg (y) (v w) : g.inner y v w =
      (F.parameters.h a)⁻¹ ^ 2 * (F.metric a).inner y v w := rfl
  have hdomain : D.chart.source ⊆ F.standard_initial.metric.ball 0 D.eta⁻¹ := by
    rw [D.chart_source]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal D.radius_lt.le)
  exact (D.ordinary.initial_pullback_eq ⟨le_rfl, D.lifetime_pos⟩
    D.chart_target_subset D.birth_identity g hg D.target_point hx).trans
      (physical_birth_pullback_eq F a ha i D.comparison g hg D.chart.open_source hdomain
        (fun y _ => D.chart_eq y) hx)

/-- Every actual birth spatial jet is the corresponding M36
comparison jet. Source: Corollary 16.7; M44 derivation 88. -/
theorem initial_spatial_jet (D : CylinderCompactnessSample g0 F a ha i)
    {x : E} (hx : x ∈ D.chart.source) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => D.coefficients (0, y)) x =
      iteratedFDeriv ℝ m D.comparison.normalizedCoefficients x := by
  have heq : (fun y => D.coefficients (0, y)) =ᶠ[𝓝 x]
      D.comparison.normalizedCoefficients :=
    eventually_of_mem (D.chart.open_source.mem_nhds hx) (fun _ hy => D.initial_coefficients hy)
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds

/-- Rewriting the fixed initial-metric label leaves the physical
comparison data unchanged. Source: Corollary 16.7; derivation 88. -/
def fixedComparison (D : CylinderCompactnessSample g0 F a ha i) :
    SurgeryCapClose g0 ((F.event a ha).local_result i).output
      ((F.event a ha).local_result i).metric ((F.event a ha).local_result i).tip
      (((F.event a ha).necks i).neck.scale) D.eta :=
  Eq.mp (congrArg (fun g : StandardInitialMetric =>
    SurgeryCapClose g ((F.event a ha).local_result i).output
      ((F.event a ha).local_result i).metric ((F.event a ha).local_result i).tip
      (((F.event a ha).necks i).neck.scale) D.eta) D.standard_initial_eq) D.comparison

end CylinderCompactnessSample

/-- Transport in the standard-initial-metric parameter leaves the
actual normalized coefficients unchanged. Source: Corollary 16.7;
the fixed initial comparison in M44 derivation 88. -/
theorem normalizedCoefficients_cast_initial
    {g0 g1 : StandardInitialMetric} (h : g0 = g1)
    {S : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 S.carrier}
    {tip : S.carrier} {scale eta : ℝ} (Q : SurgeryCapClose g0 S g tip scale eta) :
    (Eq.mp (congrArg (fun g' : StandardInitialMetric =>
      SurgeryCapClose g' S g tip scale eta) h) Q).normalizedCoefficients =
        Q.normalizedCoefficients := by
  subst g1
  rfl

end PoincareMT.M44
