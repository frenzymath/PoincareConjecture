import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Within-jet bounds at boundary points

An ambient jet bound on an interior set extends to its closure inside
the actual relative smoothness domain, with the same constant. This
retains the included endpoint in the partial-flow bounds of Morgan--Tian
Proposition 5.14, pp. 90-91, and the backward-extension argument after
Claim 10.10, p. 255. See derivation 11.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Topology

/-- An interior bound extends to boundary points as a bound for the
actual within jet. No extension of the function beyond its smoothness
domain is required (Morgan--Tian Proposition 5.14; derivation 11). -/
theorem norm_iteratedFDerivWithin_le_of_interior_bound
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {S T : Set E} {f : E → F} {n : ℕ∞ω} {m : ℕ} {B : ℝ} {x : E}
    (hf : ContDiffOn 𝕜 n f S) (hS : UniqueDiffOn 𝕜 S) (hm : m ≤ n)
    (hTS : T ⊆ interior S)
    (hbound : ∀ y ∈ T, ‖iteratedFDeriv 𝕜 m f y‖ ≤ B)
    (hx : x ∈ S) (hxT : x ∈ closure T) :
    ‖iteratedFDerivWithin 𝕜 m f S x‖ ≤ B := by
  apply ContinuousWithinAt.closure_le hxT
    (((hf.continuousOn_iteratedFDerivWithin hm hS) x hx).norm.mono
      (hTS.trans interior_subset)) continuousWithinAt_const
  intro y hy
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS
    ((hf.contDiffAt (mem_interior_iff_mem_nhds.mp (hTS hy))).of_le hm)
    (interior_subset (hTS hy))]
  exact hbound y hy
