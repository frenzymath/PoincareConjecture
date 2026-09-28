import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.RotationMaximum
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.UniformInitialTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

local notation "V" => StandardCapSpace

structure RotationHeatFamily {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (T : ℝ) (B : V →L[ℝ] V) where
  form : (j : ℕ) → ℝ → PiLp 2 (fun _ : Fin 3 => dirichletForm (rotationHeatDomain j))
  value : (j : ℕ) → ℝ → PiLp 2 (fun _ : Fin 3 => dirichletValue (rotationHeatDomain j))
  equation : ∀ j, PrincipalValueHeat (rotationHeatDomain j)
    (fun t => rawCutoffPrincipalCoefficient (G.flow.metric t)
      (rotationHeatCutoff j) (rotationHeatCutoff_compact j))
    (fun t => rawLowerFormOperator (G.flow.connection t) Metric.isClosed_closedBall
      (rotationHeatCutoff j) (rotationHeatCutoff_compact j))
    0 T (rotationInitialValue j B) (form j) (value j)
  metric_bound : ∀ j t, t ∈ Icc 0 T → ∀ᵐ x ∂volume, x ∈ rotationHeatDomain j →
    (G.flow.metric t).inner x (dirichletValueField (rotationHeatDomain j) (value j t) x)
      (dirichletValueField (rotationHeatDomain j) (value j t) x) ≤ 4 * ‖B‖ ^ 2

theorem exists_raw_rotation_heat_family (P : RicciFlowCurvatureTheory.{0})
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)
    (B : V →L[ℝ] V) (hB : ∀ x, inner ℝ x (B x) = 0) :
    Nonempty (RotationHeatFamily G T B) := by
  choose v U hs hb using exists_raw_rotation_heat_with_metric_bound P E G hT hTlt B hB
  exact ⟨⟨v, U, hs, hb⟩⟩

def RotationHeatFamily.field {g₀ : StandardInitialMetric} {G : PartialStandardCapFlow g₀}
    {T : ℝ} {B : V →L[ℝ] V} (H : RotationHeatFamily G T B) (j : ℕ) (t : ℝ) :
    Lp V 2 (volume : Measure V) := dirichletValueField (rotationHeatDomain j) (H.value j t)

theorem RotationHeatFamily.field_continuousOn {g₀ : StandardInitialMetric}
    {G : PartialStandardCapFlow g₀} {T : ℝ} {B : V →L[ℝ] V}
    (H : RotationHeatFamily G T B) (j : ℕ) : ContinuousOn (H.field j) (Icc 0 T) :=
  (dirichletValueField (rotationHeatDomain j)).continuous.comp_continuousOn (H.equation j).2.2.1

theorem exists_rotation_heat_test_radius {E : Set V} (hE : IsCompact E) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, E ⊆ Metric.closedBall 0 ((j : ℝ) + 1) := by
  obtain ⟨R, _hR, hb⟩ := hE.isBounded.exists_pos_norm_le
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt R
  refine ⟨j₀, ?_⟩
  intro j hj x hx
  change dist x 0 ≤ (j : ℝ) + 1
  rw [dist_zero_right]
  have hj' : (j₀ : ℝ) ≤ j := Nat.cast_le.mpr hj
  linarith [hb x hx]

theorem rotationInitialValue_test_pair {E : Set V}
    (f : Fin 3 → supportedTests E) (B : V →L[ℝ] V) (j : ℕ)
    (hE : E ⊆ Metric.closedBall 0 ((j : ℝ) + 1)) :
    (∫ x, inner ℝ (schwartzField (fun k => (f k : 𝓢(V, ℝ))) x)
        (dirichletValueField (rotationHeatDomain j) (rotationInitialValue j B) x)) =
      ∫ x, inner ℝ (schwartzField (fun k => (f k : 𝓢(V, ℝ))) x) (B x) := by
  apply integral_congr_ae
  filter_upwards [rotationInitialValue_coe j B] with x hx
  rw [hx]
  by_cases hxE : x ∈ E
  · rw [cutoffRotationField_eq j B (hE hxE)]
  · have hz : schwartzField (fun k => (f k : 𝓢(V, ℝ))) x = 0 := by
      rw [schwartzField_apply]
      apply PiLp.ext
      exact fun k => (f k).property x hxE
    rw [hz, inner_zero_left, inner_zero_left]

theorem RotationHeatFamily.uniform_initial_test_trace {g₀ : StandardInitialMetric}
    {G : PartialStandardCapFlow g₀} {T : ℝ} {B : V →L[ℝ] V}
    (H : RotationHeatFamily G T B) (hTlt : T < G.lifetime)
    {E : Set V} (hE : IsCompact E) (f : Fin 3 → supportedTests E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ Icc 0 T,
      ‖(∫ x, inner ℝ (schwartzField (fun k => (f k : 𝓢(V, ℝ))) x) (H.field j t x)) -
        (∫ x, inner ℝ (schwartzField (fun k => (f k : 𝓢(V, ℝ))) x) (B x))‖ ≤ M * t := by
  have hJ : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_lt hTlt⟩
  obtain ⟨M, hM, hb⟩ := exists_raw_fixed_test_initial_bound G.flow hJ hE f
    (by positivity : 0 ≤ 4 * ‖B‖ ^ 2)
  obtain ⟨j₀, hj₀⟩ := exists_rotation_heat_test_radius hE
  refine ⟨M, hM, j₀, ?_⟩
  intro j hj t ht
  have hEK : E ⊆ rotationHeatDomain j :=
    (hj₀ j hj).trans (Metric.closedBall_subset_closedBall (by linarith))
  have h := hb (rotationHeatDomain j) Metric.isClosed_closedBall hEK (rotationHeatCutoff j)
    (rotationHeatCutoff_compact j) (rotationHeatCutoff_one j) (rotationInitialValue j B)
    (H.form j) (H.value j) (H.equation j) (H.metric_bound j) t ht
  rw [rotationInitialValue_test_pair f B j (hj₀ j hj)] at h
  exact h

end PoincareConjecture.M35.Uniqueness.Heat
