import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Linear precomposition of a smooth germ

The ordinary iterated derivative of a local smooth map transforms under a
fixed continuous linear parameter map. This supplies the product-coordinate
adapter for Morgan-Tian Proposition 12.7, pp. 298-299; see
end-chart-uniform-jets.md.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The local finite-jet bound for linear precomposition, without a
global smoothness hypothesis (Proposition 12.7, pp. 298-299). -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_comp_right_of_contDiffAt
    (L : E →L[𝕜] F) {f : F → G} {x : E} {m : ℕ}
    (hf : ContDiffAt 𝕜 (m : ℕ∞ω) f (L x)) :
    ‖iteratedFDeriv 𝕜 m (f ∘ L) x‖ ≤
      ‖iteratedFDeriv 𝕜 m f (L x)‖ * ‖L‖ ^ m := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω)) le_rfl (by simp)
  obtain ⟨U, hUs, hU, hx⟩ := mem_nhds_iff.mp hs
  have hV : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right (hfs.mono hUs)
    hU.uniqueDiffOn hV.uniqueDiffOn hx le_rfl
  rw [iteratedFDerivWithin_of_isOpen m hV hx,
    iteratedFDerivWithin_of_isOpen m hU hx] at h
  rw [h]
  simpa using (iteratedFDeriv 𝕜 m f (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin m => L)
