import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormMixedHeat
import Mathlib.Analysis.Calculus.ContDiff.Operations









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {P X : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem one_sub_operator_isInvertible (A : X →L[ℝ] X) (hA : ‖A‖ < 1) :
    (1 - A).IsInvertible := by
  obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one hA
  exact ⟨ContinuousLinearEquiv.ofUnit v, hv⟩

def affineResponse (A : X →L[ℝ] X) (q : X) : X := (1 - A).inverse q

theorem affineResponse_equation (A : X →L[ℝ] X) (hA : ‖A‖ < 1) (q : X) :
    affineResponse A q = A (affineResponse A q) + q := by
  have he := (one_sub_operator_isInvertible A hA).self_apply_inverse q
  change affineResponse A q - A (affineResponse A q) = q at he
  exact sub_eq_iff_eq_add'.mp he

theorem affineResponse_eq (A : X →L[ℝ] X) (hA : ‖A‖ < 1) {q x : X}
    (hx : x = A x + q) : affineResponse A q = x := by
  apply (one_sub_operator_isInvertible A hA).inverse_apply_eq.mpr
  change q = x - A x
  exact (sub_eq_iff_eq_add'.mpr hx).symm

theorem contDiffAt_affineResponse {A : P → X →L[ℝ] X} {q : P → X} {p : P}
    (hA : ContDiffAt ℝ ∞ A p) (hq : ContDiffAt ℝ ∞ q p) (hsmall : ‖A p‖ < 1) :
    ContDiffAt ℝ ∞ (fun s => affineResponse (A s) (q s)) p := by
  have hB : ContDiffAt ℝ ∞ (fun s => (1 : X →L[ℝ] X) - A s) p :=
    contDiffAt_const.sub hA
  have hi := ((one_sub_operator_isInvertible (A p) hsmall).contDiffAt_map_inverse).comp p hB
  exact hi.clm_apply hq

omit [NormedSpace ℝ P] in
theorem affineResponse_equation_eventually {A : P → X →L[ℝ] X} {q : P → X} {p : P}
    (hA : ContinuousAt A p) (hsmall : ‖A p‖ < 1) :
    ∀ᶠ s in 𝓝 p, affineResponse (A s) (q s) = A s (affineResponse (A s) (q s)) + q s := by
  filter_upwards [hA.norm.eventually (gt_mem_nhds hsmall)] with s hs
  exact affineResponse_equation (A s) hs (q s)

end PoincareConjecture.M35.Uniqueness.Heat
