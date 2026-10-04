import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Compactness.CylinderCompactnessFeedData
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Construction.RescaledLimitCurvature
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Terminal.TerminalCylinderJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.CylinderUniqueness

/-!
# Agreement of actual cylinder samples on their common chart

The same physical birth comparison gives identical tracked trajectories,
normalized coefficient germs and spatial jets. Curvature bounds transfer
to every smaller chart throughout the common lifetime.
Morgan--Tian, Claim 16.6 and Lemma 16.8, pp. 371-373;
M44 derivation 97.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44.CylinderCompactnessSample

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance sampleAgreementCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sampleAgreementCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a : ℝ}
  {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
  {i : Fin (F.event a ha).cap_count}

/-- Equality of the supplied comparison maps retains the literal
physical birth-chart map. Source: Claim 16.6 and Lemma 16.8;
M44 derivation 97. -/
theorem chart_eq_of_comparison_map_eq
    (D₁ D₂ : CylinderCompactnessSample g0 F a ha i)
    (hmap : D₁.comparison.map = D₂.comparison.map) (x : E) :
    D₁.chart x = D₂.chart x := by
  rw [D₁.chart_eq, D₂.chart_eq, hmap]

/-- Actual tracked chart points agree on the common time and
space domain. Source: Claim 16.6 and Lemma 16.8;
M44 derivation 97. -/
theorem forward_chart_eq_of_comparison_map_eq
    (D₁ D₂ : CylinderCompactnessSample g0 F a ha i)
    (hmap : D₁.comparison.map = D₂.comparison.map)
    {s : ℝ} (hs₁ : s ∈ Ico 0 D₁.lifetime) (hs₂ : s ∈ Ico 0 D₂.lifetime)
    {x : E} (hx₁ : x ∈ D₁.chart.source) (hx₂ : x ∈ D₂.chart.source) :
    D₁.cylinder.forward s hs₁ (D₁.chart x) =
      D₂.cylinder.forward s hs₂ (D₂.chart x) := by
  have hI : Icc 0 s ⊆ Ico 0 D₁.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_lt hs₁.2⟩
  have hJ : Icc 0 s ⊆ Ico 0 D₂.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_lt hs₂.2⟩
  have hy₁ : D₁.chart x ∈ D₁.region := D₁.chart_target_subset (D₁.chart.map_source hx₁)
  have hchart := D₁.chart_eq_of_comparison_map_eq D₂ hmap x
  have hy₂ : D₁.chart x ∈ D₂.region := by
    rw [hchart]
    exact D₂.chart_target_subset (D₂.chart.map_source hx₂)
  have hinit : D₁.cylinder.forward 0 (hI ⟨le_rfl, hs₁.1⟩) (D₁.chart x) =
      D₂.cylinder.forward 0 (hJ ⟨le_rfl, hs₁.1⟩) (D₁.chart x) :=
    eq_of_heq ((D₁.birth_identity _ _ hy₁).trans (D₂.birth_identity _ _ hy₂).symm)
  have h := cylinder_forward_eq_of_initial D₁.cylinder D₂.cylinder hs₁.1 hI hJ
    (D₁.chart x) hy₁ hy₂ hinit
  simpa only [hchart] using h

/-- The actual normalized coefficients agree at each common
chart point and time. Source: Claim 16.6 and Lemma 16.8;
M44 derivation 97. -/
theorem coefficients_eq_of_comparison_map_eq
    (D₁ D₂ : CylinderCompactnessSample g0 F a ha i)
    (hmap : D₁.comparison.map = D₂.comparison.map)
    {s : ℝ} (hs₁ : s ∈ Ico 0 D₁.lifetime) (hs₂ : s ∈ Ico 0 D₂.lifetime)
    {x : E} (hx₁ : x ∈ D₁.chart.source) (hx₂ : x ∈ D₂.chart.source) :
    D₁.coefficients (s, x) = D₂.coefficients (s, x) := by
  have heq : D₁.cylinder.forward s hs₁ ∘ D₁.chart =ᶠ[𝓝 x]
      D₂.cylinder.forward s hs₂ ∘ D₂.chart := by
    filter_upwards [D₁.chart.open_source.mem_nhds hx₁,
      D₂.chart.open_source.mem_nhds hx₂] with y hy₁ hy₂
    exact D₁.forward_chart_eq_of_comparison_map_eq D₂ hmap hs₁ hs₂ hy₁ hy₂
  unfold coefficients
  rw [D₁.ordinary.normalized_coefficients_eq D₁.chart_target_subset D₁.target_point s hs₁ hx₁,
    D₂.ordinary.normalized_coefficients_eq D₂.chart_target_subset D₂.target_point s hs₂ hx₂]
  congr 1
  exact pullbackCoefficients_congr_of_eventuallyEq _ heq

/-- Every spatial jet agrees on the open overlap of actual birth
charts. Source: Claim 16.6 and Lemma 16.8; derivation 97. -/
theorem spatial_jet_eq_of_comparison_map_eq
    (D₁ D₂ : CylinderCompactnessSample g0 F a ha i)
    (hmap : D₁.comparison.map = D₂.comparison.map)
    {s : ℝ} (hs₁ : s ∈ Ico 0 D₁.lifetime) (hs₂ : s ∈ Ico 0 D₂.lifetime)
    {x : E} (hx₁ : x ∈ D₁.chart.source) (hx₂ : x ∈ D₂.chart.source) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => D₁.coefficients (s, y)) x =
      iteratedFDeriv ℝ m (fun y => D₂.coefficients (s, y)) x := by
  have heq : (fun y => D₁.coefficients (s, y)) =ᶠ[𝓝 x]
      (fun y => D₂.coefficients (s, y)) := by
    filter_upwards [D₁.chart.open_source.mem_nhds hx₁,
      D₂.chart.open_source.mem_nhds hx₂] with y hy₁ hy₂
    exact D₁.coefficients_eq_of_comparison_map_eq D₂ hmap hs₁ hs₂ hy₁ hy₂
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds

/-- The native coefficient two-jet agrees on the same actual
sample overlap. Source: Lemma 16.8; M44 derivation 97. -/
theorem twoJet_eq_of_comparison_map_eq
    (D₁ D₂ : CylinderCompactnessSample g0 F a ha i)
    (hmap : D₁.comparison.map = D₂.comparison.map)
    {s : ℝ} (hs₁ : s ∈ Ico 0 D₁.lifetime) (hs₂ : s ∈ Ico 0 D₂.lifetime)
    {x : E} (hx₁ : x ∈ D₁.chart.source) (hx₂ : x ∈ D₂.chart.source) :
    metricTwoJet (fun y => D₁.coefficients (s, y)) x =
      metricTwoJet (fun y => D₂.coefficients (s, y)) x := by
  have heq : (fun y => D₁.coefficients (s, y)) =ᶠ[𝓝 x]
      (fun y => D₂.coefficients (s, y)) := by
    filter_upwards [D₁.chart.open_source.mem_nhds hx₁,
      D₂.chart.open_source.mem_nhds hx₂] with y hy₁ hy₂
    exact D₁.coefficients_eq_of_comparison_map_eq D₂ hmap hs₁ hs₂ hy₁ hy₂
  simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
    (heq.fderiv (𝕜 := ℝ)).fderiv_eq]

/-- The coefficient curvature readout is the curvature of the
actual physical chart at every source point. Source: Lemma 16.8;
M44 derivation 97. -/
theorem curvatureTensorNorm_eq_coefficient_twoJet
    (D : CylinderCompactnessSample g0 F a ha i)
    (s : ℝ) {x : E} (hx : x ∈ D.chart.source) :
    (D.ordinary.flow.connection s).curvatureTensorNorm (targetChart D.chart D.target_point x) =
      standardJetCurvatureNorm (metricTwoJet (fun y => D.coefficients (s, y)) x) := by
  exact (standardJetCurvatureNorm_pullbackCoefficients
    (D.ordinary.flow.metric s) (D.ordinary.flow.connection s)
    D.chart.open_source (contMDiffOn_targetChart D.chart D.target_point)
    (fun _ hy => D.target_derivative_invertible hy) hx).symm

/-- A bound on the larger actual sample controls the whole
smaller sample throughout their common lifetime, with the same
constant. Source: Claim 16.6 and Lemma 16.8; derivation 97. -/
theorem curvature_bound_of_radius_le
    (D₁ D₂ : CylinderCompactnessSample g0 F a ha i)
    (hmap : D₁.comparison.map = D₂.comparison.map) (hR : D₁.radius ≤ D₂.radius)
    {s K : ℝ} (hs₁ : s ∈ Ico 0 D₁.lifetime) (hs₂ : s ∈ Ico 0 D₂.lifetime)
    (hbound : ∀ y, (D₂.ordinary.flow.connection s).curvatureTensorNorm y ≤ K) :
    ∀ y, (D₁.ordinary.flow.connection s).curvatureTensorNorm y ≤ K := by
  intro y
  let x := D₁.chart.symm y.1
  have hx₁ : x ∈ D₁.chart.source := D₁.chart.map_target y.2
  have hx₂ : x ∈ D₂.chart.source := by
    rw [D₁.source_eq] at hx₁
    rw [D₂.source_eq]
    exact hx₁.trans_le (ENNReal.ofReal_le_ofReal hR)
  have hpoint : targetChart D₁.chart D₁.target_point x = y := by
    apply Subtype.ext
    rw [targetChart_val D₁.chart D₁.target_point hx₁]
    exact D₁.chart.right_inv y.2
  rw [← hpoint, D₁.curvatureTensorNorm_eq_coefficient_twoJet s hx₁,
    D₁.twoJet_eq_of_comparison_map_eq D₂ hmap hs₁ hs₂ hx₁ hx₂,
    ← D₂.curvatureTensorNorm_eq_coefficient_twoJet s hx₂]
  exact hbound _

end PoincareMT.M44.CylinderCompactnessSample
