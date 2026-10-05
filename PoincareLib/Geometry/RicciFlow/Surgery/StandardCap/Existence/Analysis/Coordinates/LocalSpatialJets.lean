import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.AffineWithinJets

/-!
# Spatial extraction on a local part of the frozen domain

An open spatial restriction does not change a within-domain jet at
one of its points. This permits local regularity on an exhaustion stage
while retaining the larger coordinate domain of the convergence data.
Source: Morgan-Tian Theorems 11.8 and 12.28, pp. 276-277, 323-324;
M34 canonical-neighborhood persistence derivation, section 3.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

/-- Local spatial smoothness identifies a slice jet with the actual
joint within jet on a larger spatial domain (Theorem 12.28). -/
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
