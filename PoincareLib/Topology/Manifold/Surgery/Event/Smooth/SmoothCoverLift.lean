import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smoothness of continuous lifts through local diffeomorphisms

This local inverse argument allows a sphere fiber in the base to be lifted
to the actual circle pullback with its lifted atlas.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

namespace PoincareMT.M38

/-- A continuous lift is smooth whenever its projection through a smooth
local diffeomorphism is smooth. The source model may have any dimension. -/
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

end PoincareMT.M38
