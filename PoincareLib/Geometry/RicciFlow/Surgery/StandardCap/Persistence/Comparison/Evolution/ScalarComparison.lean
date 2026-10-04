import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Comparison.Evolution.ScalarComparisonModel
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Compactness.CylinderCompactnessFeedData
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Terminal.TerminalScalar

/-!
# Actual scalar control from standard two-jet comparison

Finite spatial-jet comparison controls the native metric two-jet.
Its scalar readout is the scalar of the actual normalized physical
flow. Uniform comparison on a fixed whole birth chart therefore
supplies the scalar input for the restart theorem. Morgan--Tian,
Corollary 16.9, p. 373; M44 derivation 99.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Native two-jets retain nested continuous-linear coefficient slots.
set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance scalarComparisonCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance scalarComparisonCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance scalarComparisonTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance scalarComparisonTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

namespace CylinderCompactnessSample

variable {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a : ℝ}
  {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
  {i : Fin (F.event a ha).cap_count}

/-- The scalar readout is the actual physical normalized scalar,
using local metric realization and curvature naturality. Source:
Corollary 16.9, p. 373; M44 derivation 99. -/
theorem scalar_eq_jetScalarCurvature (D : CylinderCompactnessSample g0 F a ha i)
    (t : ℝ) {x : E} (hx : x ∈ D.chart.source) :
    (D.ordinary.flow.connection t).scalarCurvature (targetChart D.chart D.target_point x) =
      jetScalarCurvature (metricTwoJet (fun y => D.coefficients (t, y)) x) := by
  symm
  exact jetScalarCurvature_pullbackCoefficients
    (D.ordinary.flow.metric t) (D.ordinary.flow.connection t) D.chart.open_source
    (contMDiffOn_targetChart D.chart D.target_point)
    (fun _ hy => D.target_derivative_invertible hy) hx

/-- A scalar two-jet bound on every source point controls the
whole literal physical chart target. Source: the restarted scalar
estimate in Corollary 16.9; M44 derivation 99. -/
theorem scalar_le_of_source_twoJet_bound (D : CylinderCompactnessSample g0 F a ha i)
    (t : ℝ) {M : ℝ}
    (hbound : ∀ x ∈ D.chart.source,
      jetScalarCurvature (metricTwoJet (fun y => D.coefficients (t, y)) x) ≤ M) :
    ∀ y, (D.ordinary.flow.connection t).scalarCurvature y ≤ M := by
  intro y
  have hx := D.chart.map_target y.2
  have h := (D.scalar_eq_jetScalarCurvature t hx).trans_le (hbound _ hx)
  have heq : targetChart D.chart D.target_point (D.chart.invFun y.1) = y := by
    apply Subtype.ext
    exact (targetChart_val D.chart D.target_point hx).trans (D.chart.right_inv y.2)
  change (D.ordinary.flow.connection t).scalarCurvature
    (targetChart D.chart D.target_point (D.chart.invFun y.1)) ≤ M at h
  simpa only [heq] using h

end CylinderCompactnessSample

variable {g0 : StandardInitialMetric} {F : ℕ → SurgeryFlowData.{u}}
  {a : ℕ → ℝ} {ha : ∀ k, a k ∈ (F k).surgery_times}
  [∀ k, Nonempty ((F k).slice (a k)).carrier]
  {i : ∀ k, Fin ((F k).event (a k) (ha k)).cap_count}

/-- Uniform actual spatial-jet comparison through order two gives
one common native two-jet comparison tail. It applies to fixed or
moving time sets and to compact collars and spheres. Source:
Corollary 16.9, p. 373; M44 derivation 99. -/
theorem eventually_cylinder_twoJet_comparison
    (S : RepairedStandardCapExistenceData g0)
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    (J : ℕ → Set ℝ) (C : ℕ → Set E)
    (hjets : ∀ m : ℕ, m ≤ 2 → ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
      ∀ t ∈ J k, ∀ x ∈ C k,
        ‖iteratedFDeriv ℝ m (fun y => (D k).coefficients (t, y)) x -
          iteratedFDeriv ℝ m (S.flow.metric t).euclideanCoefficients x‖ < epsilon)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ k in atTop, ∀ t ∈ J k, ∀ x ∈ C k,
      ‖metricTwoJet (fun y => (D k).coefficients (t, y)) x -
        metricTwoJet (S.flow.metric t).euclideanCoefficients x‖ ≤ delta := by
  filter_upwards [hjets 0 (by omega) delta hdelta, hjets 1 (by omega) delta hdelta,
    hjets 2 le_rfl delta hdelta] with k h0 h1 h2
  intro t ht x hx
  apply norm_metricTwoJet_sub_le
  intro m hm
  interval_cases m
  · exact (h0 t ht x hx).le
  · exact (h1 t ht x hx).le
  · exact (h2 t ht x hx).le

/-- The global standard scalar ceiling controls every source point
in a fixed compact region along a common sequence tail. Source:
Corollary 16.9, p. 373; M44 derivation 99. -/
theorem eventually_cylinder_scalar_on_compact
    (S : RepairedStandardCapExistenceData g0)
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    {H M : ℝ} (hH1 : H < 1)
    (hmodel : ∀ t ∈ Icc (0 : ℝ) H, ∀ x : E,
      (S.flow.connection t).scalarCurvature x ≤ M)
    (J : ℕ → Set ℝ) (hJ : ∀ k, J k ⊆ Icc (0 : ℝ) H)
    {C : Set E} (hC : IsCompact C)
    (hjets : ∀ m : ℕ, m ≤ 2 → ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
      ∀ t ∈ J k, ∀ x ∈ C, x ∈ (D k).chart.source →
        ‖iteratedFDeriv ℝ m (fun y => (D k).coefficients (t, y)) x -
          iteratedFDeriv ℝ m (S.flow.metric t).euclideanCoefficients x‖ < epsilon) :
    ∀ᶠ k in atTop, ∀ t ∈ J k, ∀ x ∈ C, x ∈ (D k).chart.source →
      ((D k).ordinary.flow.connection t).scalarCurvature
        (targetChart (D k).chart (D k).target_point x) ≤ M + 1 := by
  obtain ⟨delta, hdelta, hmargin⟩ :=
    exists_standard_scalar_comparison_tolerance S hH1 hmodel hC
  have hnear := eventually_cylinder_twoJet_comparison S D J
    (fun k => C ∩ (D k).chart.source)
    (fun m hm epsilon hepsilon => (hjets m hm epsilon hepsilon).mono
      fun k hk t ht x hx => hk t ht x hx.1 hx.2) hdelta
  filter_upwards [hnear] with k hk
  intro t ht x hx hsource
  rw [(D k).scalar_eq_jetScalarCurvature t hsource]
  exact (hmargin t (hJ k ht) x hx _ (hk t ht x ⟨hx, hsource⟩)).le

/-- Comparison on a compact set containing each full fixed birth
chart controls the entire physical target at every compared time.
The scalar ceiling is the previously selected global one. Source:
Corollary 16.9 and the scalar restart in Lemma 16.8;
M44 derivation 99. -/
theorem eventually_cylinder_whole_target_scalar_bound
    (S : RepairedStandardCapExistenceData g0)
    (D : ∀ k, CylinderCompactnessSample g0 (F k) (a k) (ha k) (i k))
    {H M : ℝ} (hH1 : H < 1)
    (hmodel : ∀ t ∈ Icc (0 : ℝ) H, ∀ x : E,
      (S.flow.connection t).scalarCurvature x ≤ M)
    (J : ℕ → Set ℝ) (hJ : ∀ k, J k ⊆ Icc (0 : ℝ) H)
    {C : Set E} (hC : IsCompact C)
    (hsource : ∀ᶠ k in atTop, (D k).chart.source ⊆ C)
    (hjets : ∀ m : ℕ, m ≤ 2 → ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
      ∀ t ∈ J k, ∀ x ∈ C, x ∈ (D k).chart.source →
        ‖iteratedFDeriv ℝ m (fun y => (D k).coefficients (t, y)) x -
          iteratedFDeriv ℝ m (S.flow.metric t).euclideanCoefficients x‖ < epsilon) :
    ∀ᶠ k in atTop, ∀ t ∈ J k, ∀ y,
      ((D k).ordinary.flow.connection t).scalarCurvature y ≤ M + 1 := by
  filter_upwards [eventually_cylinder_scalar_on_compact S D hH1 hmodel J hJ hC hjets,
    hsource] with k hk hsourcek
  intro t ht
  apply (D k).scalar_le_of_source_twoJet_bound
  intro x hx
  rw [← (D k).scalar_eq_jetScalarCurvature t hx]
  exact hk t ht x (hsourcek hx) hx

end PoincareMT.M44
