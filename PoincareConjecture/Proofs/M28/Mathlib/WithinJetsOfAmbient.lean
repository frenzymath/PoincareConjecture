import PoincareConjecture.Proofs.M28.Mathlib.SpatialJetsWithin

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

theorem TendstoUniformlyOn.withinJets_of_ambient
    {𝕜 E F α : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {l : Filter α} {S K : Set E} {f : α → E → F} {g : E → F} {m : ℕ}
    (hjet : TendstoUniformlyOn (fun k => iteratedFDeriv 𝕜 m (f k))
      (iteratedFDeriv 𝕜 m g) l K)
    (hS : UniqueDiffOn 𝕜 S) (hKS : K ⊆ S)
    (hf : ∀ᶠ k in l, ∀ x ∈ K, ContDiffAt 𝕜 m (f k) x)
    (hg : ∀ x ∈ K, ContDiffAt 𝕜 m g x) :
    TendstoUniformlyOn (fun k => iteratedFDerivWithin 𝕜 m (f k) S)
      (iteratedFDerivWithin 𝕜 m g S) l K := by
  apply (hjet.congr ?_).congr_right ?_
  · filter_upwards [hf] with k hk x hx
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hS (hk x hx) (hKS hx)).symm
  · intro x hx
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hS (hg x hx) (hKS hx)).symm

theorem iteratedFDerivWithin_prod_eq_of_isOpen
    {𝕜 T E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : T × E → F) (m : ℕ) {J : Set T} {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) {p : T × E}
    (hpU : p.2 ∈ U) (hpV : p.2 ∈ V) :
    iteratedFDerivWithin 𝕜 m f (J ×ˢ U) p =
      iteratedFDerivWithin 𝕜 m f (J ×ˢ V) p := by
  have hnear : J ×ˢ U =ᶠ[𝓝 p] J ×ˢ V := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hU.mem_nhds hpU),
      continuousAt_snd.preimage_mem_nhds (hV.mem_nhds hpV)] with z hzU hzV
    change z.2 ∈ U at hzU
    change z.2 ∈ V at hzV
    apply propext
    change (z ∈ J ×ˢ U) ↔ (z ∈ J ×ˢ V)
    simp only [mem_prod, hzU, hzV]
  exact iteratedFDerivWithin_congr_set hnear m
