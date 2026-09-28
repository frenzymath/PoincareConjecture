import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.InteriorMetricMaximum
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RotationCutoffs
import PoincareConjecture.Proofs.M35.RawFlow.SectionalPreservation
import PoincareConjecture.Proofs.M04.PointwiseFlatness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

local notation "V" => StandardCapSpace

def rotationHeatDomain (j : ℕ) : Set V := Metric.closedBall 0 ((j : ℝ) + 2)

def rotationHeatCutoff (j : ℕ) : 𝓢(V, ℝ) := rotationCutoffSchwartz (j + 1)

theorem rotationHeatCutoff_compact (j : ℕ) : HasCompactSupport (rotationHeatCutoff j) :=
  (rotationCutoff (j + 1)).hasCompactSupport

theorem rotationHeatCutoff_one (j : ℕ) :
    ∀ x ∈ rotationHeatDomain j, rotationHeatCutoff j x = 1 := by
  intro x hx
  apply (rotationCutoff (j + 1)).one_of_mem_closedBall
  have hr : (rotationCutoff (j + 1)).rIn = (j : ℝ) + 2 := by
    simp only [rotationCutoff, Nat.cast_add, Nat.cast_one]
    ring
  rw [hr]
  exact hx

def rotationInitialValue (j : ℕ) (B : V →L[ℝ] V) :
    PiLp 2 (fun _ : Fin 3 => dirichletValue (rotationHeatDomain j)) :=
  finiteHilbertMap (dirichletInclusion (rotationHeatDomain j)) (rotationInitialForm j B)

theorem rotationInitialValue_coe (j : ℕ) (B : V →L[ℝ] V) :
    dirichletValueField (rotationHeatDomain j) (rotationInitialValue j B) =ᵐ[volume]
      cutoffRotationField j B := by
  have hv : dirichletValueField (rotationHeatDomain j) (rotationInitialValue j B) =
      dirichletFieldValue (rotationHeatDomain j)
        (vectorTestForm (rotationHeatDomain j) (rotationInitialTest j B)) := rfl
  have he := hv.trans (dirichletFieldValue_test (rotationHeatDomain j) (rotationInitialTest j B))
  rw [he]
  filter_upwards [(schwartzField (fun i => (rotationInitialTest j B i : 𝓢(V, ℝ)))).coeFn_toLp
    2 volume] with x hx
  rw [hx, schwartzField_apply]
  rfl

theorem rotationInitialValue_metric_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (G : PartialStandardCapFlow g₀)
    (B : V →L[ℝ] V) (hB : ∀ x, inner ℝ x (B x) = 0) (j : ℕ) :
    ∀ᵐ x ∂volume, (G.flow.metric 0).inner x
      (dirichletValueField (rotationHeatDomain j) (rotationInitialValue j B) x)
      (dirichletValueField (rotationHeatDomain j) (rotationInitialValue j B) x) ≤ 4 * ‖B‖ ^ 2 := by
  filter_upwards [rotationInitialValue_coe j B] with x hx
  rw [hx, G.initial_metric]
  exact cutoffRotationField_initial_normSq_le P E B hB j x

theorem exists_raw_rotation_heat_with_metric_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (G : PartialStandardCapFlow g₀)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)
    (B : V →L[ℝ] V) (hB : ∀ x, inner ℝ x (B x) = 0) (j : ℕ) :
    ∃ v U, PrincipalValueHeat (rotationHeatDomain j)
      (fun t => rawCutoffPrincipalCoefficient (G.flow.metric t)
        (rotationHeatCutoff j) (rotationHeatCutoff_compact j))
      (fun t => rawLowerFormOperator (G.flow.connection t) Metric.isClosed_closedBall
        (rotationHeatCutoff j) (rotationHeatCutoff_compact j))
      0 T (rotationInitialValue j B) v U ∧
      ∀ t ∈ Icc 0 T, ∀ᵐ x ∂volume, x ∈ rotationHeatDomain j →
        (G.flow.metric t).inner x (dirichletValueField (rotationHeatDomain j) (U t) x)
          (dirichletValueField (rotationHeatDomain j) (U t) x) ≤ 4 * ‖B‖ ^ 2 := by
  have hJ : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_lt hTlt⟩
  have hη1 : ∀ x, ‖rotationHeatCutoff j x‖ ≤ 1 := by
    intro x
    change ‖rotationCutoff (j + 1) x‖ ≤ 1
    rw [Real.norm_of_nonneg (rotationCutoff (j + 1)).nonneg]
    exact (rotationCutoff (j + 1)).le_one
  obtain ⟨v, U, hsol⟩ := exists_raw_compact_vector_heat_on_slab G.flow hT.le hJ
    (isCompact_closedBall (0 : V) ((j : ℝ) + 2)) (rotationHeatCutoff j)
    (rotationHeatCutoff_compact j) hη1 (rotationHeatCutoff_one j) (rotationInitialValue j B)
  have hs : PrincipalValueHeat (rotationHeatDomain j)
      (fun t => rawCutoffPrincipalCoefficient (G.flow.metric t)
        (rotationHeatCutoff j) (rotationHeatCutoff_compact j))
      (fun t => rawLowerFormOperator (G.flow.connection t) Metric.isClosed_closedBall
        (rotationHeatCutoff j) (rotationHeatCutoff_compact j))
      0 T (rotationInitialValue j B) v U := by
    simpa only [sub_zero, rotationHeatDomain] using! hsol
  refine ⟨v, U, hs, ?_⟩
  have hR : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ (G.flow.connection t).scalarCurvature x := by
    intro t ht x
    exact M04.nonneg_scalar_of_nonnegativeSectionalAt (G.flow.connection t) x
      (raw_nonnegative_sectional P G (hJ ht) x)
  simpa only [sub_zero, rotationHeatDomain] using!
    raw_compact_vector_heat_metric_maximum G.flow hT hJ
    (isCompact_closedBall (0 : V) ((j : ℝ) + 2)) (rotationHeatCutoff j)
    (rotationHeatCutoff_compact j) (fun _ => (rotationCutoff (j + 1)).nonneg)
    (rotationHeatCutoff_one j) hR hsol (by positivity : 0 ≤ 4 * ‖B‖ ^ 2)
    (rotationInitialValue_metric_bound P E G B hB j)

end PoincareConjecture.M35.Uniqueness.Heat
