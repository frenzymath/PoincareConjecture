import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.MetricSpace.Thickening











set_option autoImplicit false

open Set
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem Continuous.exists_contDiff_eqOn_mem_open {f : E → F} (hf : Continuous f)
    (n : ℕ∞) {C S U : Set E} (hC : IsCompact C) (hS : IsClosed S)
    (hU : U ∈ 𝓝ˢ S) (hfU : ContDiffOn ℝ n f U)
    {T : Set F} (hT : IsOpen T) (hmem : MapsTo f C T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ n g ∧ EqOn g f S ∧
      (∀ x, dist (g x) (f x) < ε) ∧ MapsTo g C T := by
  obtain ⟨δ, hδ, hthick⟩ := (hC.image hf).exists_thickening_subset_open hT
    (image_subset_iff.mpr hmem)
  obtain ⟨g, hg, happrox, heq, _⟩ := hf.exists_contDiff_approx_and_eqOn n
    (show Continuous (fun _ : E => min ε δ) from continuous_const)
    (fun _ => lt_min hε hδ) hS hU hfU
  refine ⟨g, hg, heq, fun x => (happrox x).trans_le (min_le_left ε δ), fun x hx => ?_⟩
  apply hthick
  exact Metric.mem_thickening_iff.mpr
    ⟨f x, mem_image_of_mem f hx, (happrox x).trans_le (min_le_right ε δ)⟩
