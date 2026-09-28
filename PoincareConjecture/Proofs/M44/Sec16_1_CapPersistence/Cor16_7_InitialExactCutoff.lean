import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_UniformExactComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_PhysicalInitialChart










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture





theorem exists_initial_cap_exact_comparison_cutoff
    (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants)
    {tolerance : ℝ} (htol : 0 < tolerance) :
    ∃ deltaBar : ℝ, 0 < deltaBar ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g₀ →
        F.local_constants = K →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times)
          [Nonempty (F.slice t).carrier], F.parameters.delta t ≤ deltaBar →
          ∀ i : Fin (F.event t hT).cap_count,
            ∃ Q : SurgeryCapClose F.standard_initial
              ((F.event t hT).local_result i).output
              ((F.event t hT).local_result i).metric
              ((F.event t hT).local_result i).tip
              (((F.event t hT).necks i).neck.scale) tolerance,
              ((F.event t hT).necks i).neck.epsilon ≤
                F.local_constants.comparison_delta tolerance ∧
              ∀ r : ℝ, 0 < r → r ≤ tolerance⁻¹ →
                Q.map '' F.standard_initial.metric.ball 0 r =
                  ((F.event t hT).local_result i).metric.ball
                    ((F.event t hT).local_result i).tip
                    (((F.event t hT).necks i).neck.scale * r) := by
  obtain ⟨delta, hdelta, hrefine⟩ :=
    M44.exists_initial_exact_comparison_threshold.{u} g₀ htol
  refine ⟨min (K.comparison_delta delta) (K.comparison_delta tolerance),
    lt_min (K.comparison_delta_pos delta hdelta)
      (K.comparison_delta_pos tolerance htol), ?_⟩
  intro F hg₀ hK t hT _ hsmall i
  have hinput : ((F.event t hT).necks i).neck.epsilon ≤
      F.local_constants.comparison_delta delta := by
    rw [(F.event t hT).neck_delta i, hK]
    exact hsmall.trans (min_le_left _ _)
  have houtput : ((F.event t hT).necks i).neck.epsilon ≤
      F.local_constants.comparison_delta tolerance := by
    rw [(F.event t hT).neck_delta i, hK]
    exact hsmall.trans (min_le_right _ _)
  obtain ⟨Q⟩ := ((F.event t hT).local_result i).standard_close delta hdelta hinput
  rw [← hg₀] at hrefine
  obtain ⟨Q', hballs⟩ := hrefine _ _ _ _ delta Q le_rfl
  exact ⟨Q', houtput, hballs⟩





theorem exists_initial_cap_exact_chart_cutoff
    (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants)
    {A : ℝ} (hA : 0 < A) :
    ∃ deltaBar : ℝ, 0 < deltaBar ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g₀ →
        F.local_constants = K →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times)
          [Nonempty (F.slice t).carrier], F.parameters.delta t ≤ deltaBar →
          ∀ i : Fin (F.event t hT).cap_count,
            ∃ initial : SurgeryCapInitialComparison F t hT i A,
              initial.chart '' F.standard_initial.metric.ball 0 A =
                (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) := by
  let tolerance : ℝ := (A + 1)⁻¹
  have htol : 0 < tolerance := inv_pos.mpr (by linarith)
  have hfit : A < tolerance⁻¹ := by
    dsimp [tolerance]
    rw [inv_inv]
    linarith
  obtain ⟨deltaBar, hdelta, hcomparison⟩ :=
    exists_initial_cap_exact_comparison_cutoff.{u} g₀ K htol
  refine ⟨deltaBar, hdelta, ?_⟩
  intro F hg₀ hK t hT _ hsmall i
  obtain ⟨Q, hlink, hballs⟩ := hcomparison F hg₀ hK t hT hsmall i
  exact initial_cap_chart_of_exact_comparison F t hT i hA hfit Q hlink
    (hballs A hA hfit.le)

end PoincareConjecture
