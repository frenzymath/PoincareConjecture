import PoincareConjecture.Definitions.Ch11.BlowupLimits
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

theorem continuous_lift_smooth
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    {A Q : GeneralizedSliceCarrier}
    (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (L : M → A.carrier) (hL : Continuous L)
    (hc : ContMDiff I (𝓡 3) ∞ (q ∘ L)) : ContMDiff I (𝓡 3) ∞ L := by
  intro p
  let h := hq (L p)
  have hs := h.localInverse_contMDiffAt.comp p (hc p)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hL.continuousAt.preimage_mem_nhds
    (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)] with x hx
  exact (h.localInverse_left_inv hx).symm

end PoincareConjecture.M38
