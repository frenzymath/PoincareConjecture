import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereDiskComplement










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]




theorem IsFinitePL.sphere_disk_complement
    {S : Set E} {C : Set F} {e : S ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3) {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hdS : d ⊆ S)
    (hout : (S \ d).Nonempty) :
    IsFinitePLBallPair (ℝ × ℝ) (S \ (d \ q)) q := by
  have hecopy := he
  obtain ⟨f, hf, heval⟩ := hecopy
  obtain ⟨g, hg, hgval⟩ := he.symm
  have hgf : LeftInvOn g f S := by
    intro x hx
    rw [← heval ⟨x, hx⟩, ← hgval, e.symm_apply_apply]
  have hfg : LeftInvOn f g (frontier C) := by
    intro y hy
    rw [← hgval ⟨y, hy⟩, ← heval, e.apply_symm_apply]
  have hfS : f '' S = frontier C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← heval ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← heval, e.apply_symm_apply]
  have hback (U : Set E) (hUS : U ⊆ S) : g '' (f '' U) = U := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rwa [hgf (hUS hy)]
    · intro hx
      exact ⟨f x, mem_image_of_mem f hx, hgf (hUS hx)⟩
  have hgS : g '' frontier C = S := by rw [← hfS, hback S subset_rfl]
  have hd' := hd.image_of_subset hf hdS hgf.injOn
  have hdf : f '' d ⊆ frontier C := (image_mono hdS).trans hfS.subset
  obtain ⟨p, hpS, hpd⟩ := hout
  have hout' : (frontier C \ f '' d).Nonempty := by
    refine ⟨f p, hfS.subset (mem_image_of_mem f hpS), ?_⟩
    rintro ⟨x, hx, hxp⟩
    exact hpd (hgf.injOn (hdS hx) hpS hxp ▸ hx)
  have hgcopy := hg
  obtain ⟨K, hK, hKC, _⟩ := hgcopy
  have hcomp := K.isFinitePLBallPair_convex_sphere_disk_complement
    hK hC hcv hne hKC hdim hd' hdf hout'
  have hresult := hcomp.image_of_subset hg sdiff_subset hfg.injOn
  have hremove : g '' (f '' d \ f '' q) = d \ q := by
    rw [(hfg.injOn.mono hdf).image_sdiff_subset (image_mono hd.1),
      hback d hdS, hback q (hd.1.trans hdS)]
  have hcarrier : g '' (frontier C \ (f '' d \ f '' q)) = S \ (d \ q) := by
    rw [hfg.injOn.image_sdiff_subset (sdiff_subset.trans hdf), hgS, hremove]
  rwa [hcarrier, hback q (hd.1.trans hdS)] at hresult

end Homeomorph
