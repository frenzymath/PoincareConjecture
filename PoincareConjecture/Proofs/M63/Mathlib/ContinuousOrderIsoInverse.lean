import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity

set_option autoImplicit false

open Set

namespace PoincareConjecture.M63

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

end PoincareConjecture.M63
