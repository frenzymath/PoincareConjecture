import PoincareConjecture.Proofs.M28.Mathlib.SpatialJetsWithin

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

theorem TendstoUniformlyOn.iteratedFDeriv_spatial_slice_varying_domain
    {𝕜 T E F ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {l : Filter ι} {Jk : ι → Set T} {J : Set T} {U : Set E}
    {K : Set (T × E)} {f : ι → T × E → F} {g : T × E → F}
    {n : ℕ∞ω} {r : ℕ}
    (hjet : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin 𝕜 r (f k) (Jk k ×ˢ U))
      (iteratedFDerivWithin 𝕜 r g (J ×ˢ U)) l K)
    (hJ : UniqueDiffOn 𝕜 J) (hU : IsOpen U) (hK : K ⊆ J ×ˢ U)
    (hJk : ∀ᶠ k in l, UniqueDiffOn 𝕜 (Jk k))
    (hKk : ∀ᶠ k in l, K ⊆ Jk k ×ˢ U)
    (hf : ∀ᶠ k in l, ContDiffOn 𝕜 n (f k) (Jk k ×ˢ U))
    (hg : ContDiffOn 𝕜 n g (J ×ˢ U)) (hr : r ≤ n) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv 𝕜 r (fun y => f k (p.1, y)) p.2)
      (fun p => iteratedFDeriv 𝕜 r (fun y => g (p.1, y)) p.2) l K := by
  let R := ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (fun _ : Fin r => ContinuousLinearMap.inr 𝕜 T E)
  have h := R.uniformContinuous.comp_tendstoUniformlyOn hjet
  apply (h.congr ?_).congr_right ?_
  · filter_upwards [hJk, hKk, hf] with k hkJ hkK hkf p hp
    exact (iteratedFDeriv_spatial_slice_eq_within hkJ hU hkf
      (hkK hp).1 (hkK hp).2 hr).symm
  · intro p hp
    exact (iteratedFDeriv_spatial_slice_eq_within hJ hU hg
      (hK hp).1 (hK hp).2 hr).symm
