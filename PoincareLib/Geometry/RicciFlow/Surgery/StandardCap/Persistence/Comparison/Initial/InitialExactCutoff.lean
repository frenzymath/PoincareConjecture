import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Comparison.Initial.UniformExactComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Comparison.Initial.PhysicalInitialChart

/-!
# Exact initial comparison at a uniform surgery cutoff

The cutoff is chosen before the surgery flow, event, and cap. It gives
an exact-ball local comparison satisfying the frozen metric link, then
an initial chart onto the actual post-surgery ball.
Morgan--Tian, Claim 16.6 and Corollary 16.7, pp. 371-372; derivation 25.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

/-- The uniform refinement and both M36 cutoffs give exact comparisons
for all actual eligible local surgery results. The displayed neck
inequality is the one required by the frozen initial metric link.
Source: Claim 16.6 and Corollary 16.7, pp. 371-372. -/
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

/-- One positive surgery cutoff supplies the frozen initial comparison
onto each requested physical ball. No exponential map, frame, or
compactness data are required from the caller.
Source: Corollary 16.7, p. 372, used in Proposition 16.5, p. 374. -/
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

end PoincareMT
