import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.FlowAlgebra
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Linear first integrals and height-preserving flows

A continuous linear coordinate whose derivative vanishes on the vector
field is constant along every integral curve. The height projection
specialization is the invariant required for the level-preserving
isotopies in Hatcher, Notes on Basic 3-Manifold Topology, Lemma 1.2, pp. 2-3.
-/

set_option autoImplicit false

open scoped NNReal

namespace PoincareMT.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear coordinate annihilating the vector field is preserved by
its flow; Hatcher's level-preserving isotopies, Lemma 1.2, pp. 2-3. -/
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

/-- A vector field with zero vertical component has a height-preserving
flow; Hatcher's horizontal cap moves, Lemma 1.2, pp. 2-3. -/
theorem boundedFlow_preserves_height (f : E × ℝ → E × ℝ) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (hz : ∀ x, (f x).2 = 0) (x : E × ℝ) (t : ℝ) :
    (boundedFlow f hK hL x t).2 = x.2 :=
  boundedFlow_preserves_linear f hK hL (ContinuousLinearMap.snd ℝ E ℝ) hz x t

end PoincareMT.M25.Topology3D
