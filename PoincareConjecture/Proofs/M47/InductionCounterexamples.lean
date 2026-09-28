import PoincareConjecture.Statements.M47CanonicalInduction
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47

theorem canonicalInduction_counterexample
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    (Q : SurgeryNoncollapseExtension.{u} p)
    (hno : ¬ Nonempty (SurgeryCanonicalExtension p Q))
    {r delta : ℝ} (hr : 0 < r) (hrLast : r ≤ p.r (Fin.last p.i))
    (hdelta : 0 < delta) (hcutoff : delta ≤ Q.cutoff r) :
    ∃ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      SurgeryObservationIsNextEpoch p O ∧ SurgeryPrefixControls p F O ∧
      SurgeryFlowAdmissible F ∧ SurgeryFlowPinched F ∧
      SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) ∧
      SurgeryPostPrefixScales p F O r delta ∧
      (∀ t ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta t ≤ delta) ∧
      ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r := by
  classical
  by_contra hnone
  apply hno
  refine ⟨{
    rNext := r
    deltaNext := delta
    r_pos := hr
    r_le_last := hrLast
    delta_pos := hdelta
    delta_le_cutoff := hcutoff
    canonical := ?_ }⟩
  intro F O hnext old admissible pinched policy scales overlap
  by_contra hbad
  exact hnone ⟨F, O, hnext, old, admissible, pinched, policy, scales, overlap, hbad⟩

theorem canonicalInduction_radius_bounds {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 < r / ((n : ℝ) + 1) ∧ r / ((n : ℝ) + 1) ≤ r := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨div_pos hr hn, (div_le_iff₀ hn).mpr ?_⟩
  nlinarith only [Nat.cast_nonneg (α := ℝ) n, hr]

theorem canonicalInduction_radius_tendsto (r : ℝ) :
    Tendsto (fun n : ℕ => r / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [mul_one_div, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r

theorem canonicalInduction_scalar_diverges {r : ℝ} (hr : 0 < r)
    {Q : ℕ → ℝ} (hQ : ∀ n : ℕ, (r / ((n : ℝ) + 1))⁻¹ ^ 2 ≤ Q n) :
    Tendsto Q atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdiv : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r) atTop atTop :=
    hn.atTop_div_const hr
  have hsquare := (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hdiv
  apply tendsto_atTop_mono _ hsquare
  intro n
  simpa only [inv_div, Function.comp_apply] using hQ n

end PoincareConjecture.Proofs.M47
