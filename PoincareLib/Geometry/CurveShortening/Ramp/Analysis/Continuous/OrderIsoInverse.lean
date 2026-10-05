import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Joint continuity of inverse real labels

Increasing real bijections with continuous parameter evaluations have
jointly continuous inverse evaluations. MT2007 Claim 19.1, p. 437;
`2026-09-22-continuous-inverse-labels.md`.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M63

/-- Actual inverse labels vary jointly continuously for arbitrary
topological parameters. MT2007 Claim 19.1, p. 437; inverse-label
derivation. Only fixed-label evaluation continuity is required. -/
theorem continuous_inverse_orderIso_family {Z : Type*} [TopologicalSpace Z]
    (phi : Z → (ℝ ≃o ℝ)) (hphi : ∀ a, Continuous (fun z => phi z a)) :
    Continuous (fun p : Z × ℝ => (phi p.1).symm p.2) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  constructor
  · change IsOpen {p : Z × ℝ | a < (phi p.1).symm p.2}
    simpa only [OrderIso.lt_symm_apply, Function.comp_def] using
      isOpen_lt ((hphi a).comp continuous_fst) continuous_snd
  · change IsOpen {p : Z × ℝ | (phi p.1).symm p.2 < a}
    simpa only [OrderIso.symm_apply_lt, Function.comp_def] using
      isOpen_lt continuous_snd ((hphi a).comp continuous_fst)

end PoincareMT.M63
