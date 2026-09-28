import Mathlib.Analysis.Calculus.ContDiff.Basic










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]



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
