import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.Basic

set_option autoImplicit false

open Set TopologicalSpace

namespace PoincareConjecture.M63

theorem secondCountable_of_countable_hilbertBasis
    {iota 𝕜 E : Type*} [Countable iota] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : HilbertBasis iota 𝕜 E) :
    SecondCountableTopology E := by
  have hs := ((countable_range b).isSeparable.span (R := 𝕜)).closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] at hs
  let : SeparableSpace E := isSeparable_univ_iff.mp hs
  infer_instance

end PoincareConjecture.M63
