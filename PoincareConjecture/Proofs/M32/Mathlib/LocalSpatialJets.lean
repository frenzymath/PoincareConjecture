import PoincareConjecture.Proofs.M32.Mathlib.AffineWithinJets

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M32

theorem iteratedFDeriv_prod_slice_eq_within_of_open_subset
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : G × E → F} {J : Set G} {U V : Set E} {n : ℕ∞ω}
    (hf : ContDiffOn 𝕜 n f (J ×ˢ V)) (hJ : UniqueDiffOn 𝕜 J)
    (hV : IsOpen V) (hVU : V ⊆ U) {t : G} (ht : t ∈ J)
    {x : E} (hx : x ∈ V) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (fun y => f (t, y)) x =
      (iteratedFDerivWithin 𝕜 i f (J ×ˢ U) (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr 𝕜 G E) := by
  have hsets : (J ×ˢ V) =ᶠ[𝓝 (t, x)] (J ×ˢ U) := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hV.mem_nhds hx)] with z hz
    exact propext ⟨fun h => ⟨h.1, hVU h.2⟩, fun h => ⟨h.1, hz⟩⟩
  rw [← iteratedFDerivWithin_congr_set hsets i]
  exact iteratedFDeriv_prod_slice_eq_within hf hJ hV ht hx hi

end PoincareConjecture.M32
