import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Convergence.SampleGluing
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Support.CylinderErrorConvergence

/-!
# The uniform beta in the literal neck-gluing contract

Failure of the stated uniform producer supplies improving actual
counterexamples. Their literal squared errors tend to zero, contradicting
the fixed positive half-square lower bound. Source: Proposition 15.2,
pp. 353-354; see GluingCompactness.md for the exact finite-jet derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareMT.M45

/-- Proposition 15.2 produces one beta uniformly for every actual input
pair, retaining the recent chart and its inverse and the joint smooth
piecewise tensor over the complete normalized time window.
Source: Proposition 15.2, pp. 353-354; GluingCompactness.md. -/
theorem neckGluingProducer :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 200 →
      ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 2 ∧ M45NeckGluingProperty.{u} epsilon beta := by
  intro epsilon hepsilon _hsmall
  by_contra hnot
  obtain ⟨S, d, hd, hlim⟩ := exists_gluing_bad_sequence_duration_limit hepsilon hnot
  have hsmooth (n : ℕ) : RoundCylinderTensorSmoothOn epsilon
      ((S.input n).piecewiseTensor (S.input n).recent_patch.coordinate (S.time n)) :=
    piecewiseTensor_smooth_on_output hepsilon (S.beta_pos n)
      (by linarith [S.beta_le_quarter n]) (S.tolerance_lt_half n) (S.input n)
      (S.older_survival n).le (S.time n) (S.time_mem n)
  have hzero := tendsto_roundCylinderJetErrorSquared_zero
    (fun n => ⟨(S.time_mem n).1.le, (S.time_mem n).2⟩) hsmooth S.point_mem
    (S.piecewise_error_pointJetsVanish hepsilon hd hlim) ⌊epsilon⁻¹⌋₊
  have hnonpos : epsilon ^ 2 / 2 ≤ (0 : ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hzero
      (Eventually.of_forall (fun n => (S.bad n).le))
  linarith [sq_pos_of_pos hepsilon]

end PoincareMT.M45
