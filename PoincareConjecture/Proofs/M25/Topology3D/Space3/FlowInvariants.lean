import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowAlgebra
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open scoped NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem boundedFlow_preserves_linear (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (A : E →L[ℝ] F) (hA : ∀ x, A (f x) = 0) (x : E) (t : ℝ) :
    A (boundedFlow f hK hL x t) = A x := by
  have hd (u : ℝ) : HasDerivAt (fun s => A (boundedFlow f hK hL x s)) 0 u := by
    simpa only [Function.comp_def, hA] using
      A.hasFDerivAt.comp_hasDerivAt u (boundedFlow_hasDerivAt f hK hL x u)
  simpa only [boundedFlow_zero] using
    is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0

theorem boundedFlow_preserves_height (f : E × ℝ → E × ℝ) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (hz : ∀ x, (f x).2 = 0) (x : E × ℝ) (t : ℝ) :
    (boundedFlow f hK hL x t).2 = x.2 :=
  boundedFlow_preserves_linear f hK hL (ContinuousLinearMap.snd ℝ E ℝ) hz x t

end PoincareConjecture.M25.Topology3D
