import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Statement

/-!
# Short-loop triviality and small-area disk theory

The data package contains both the original decorated-family formulation of
Lemma 18.27 and its raw continuous-map reformulation.  The raw service is
needed by M65's output and is consumed by the ordinary width argument in M66;
it is not a second class predicate.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Morgan--Tian Lemma 18.27 and Corollary 18.28, pp. 434-435, with the
boundary convention of Definition 18.17, p. 430. The hypotheses and all
three conclusions are explicit in `RepairedShortLoopTrivialityData`. -/
structure RepairedShortLoopTrivialityTheory : Prop where
  short_loop : RepairedShortLoopTrivialityData.{u}

end PoincareMT
