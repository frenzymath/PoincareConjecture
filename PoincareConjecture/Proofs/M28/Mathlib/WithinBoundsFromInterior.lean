import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Order.OrderClosed











set_option autoImplicit false

open Set
open scoped ContDiff Topology




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
