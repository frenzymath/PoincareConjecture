import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Second countability from a countable Hilbert basis

The countable basis has separable dense span in the actual norm topology.
This supplies the Fourier coefficient space topology for MT2007
Claim 19.1, p. 437; `2026-09-21-countable-hilbert-basis.md`.
-/

set_option autoImplicit false

open Set TopologicalSpace

namespace PoincareMT.M63

/-- A countable Hilbert basis makes the actual norm topology second
countable. MT2007 Claim 19.1, p. 437; auxiliary countable Hilbert basis
derivation, using Mathlib's dense span and separable span theorems. -/
theorem secondCountable_of_countable_hilbertBasis
    {iota 𝕜 E : Type*} [Countable iota] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : HilbertBasis iota 𝕜 E) :
    SecondCountableTopology E := by
  have hs := ((countable_range b).isSeparable.span (R := 𝕜)).closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] at hs
  let : SeparableSpace E := isSeparable_univ_iff.mp hs
  infer_instance

end PoincareMT.M63
