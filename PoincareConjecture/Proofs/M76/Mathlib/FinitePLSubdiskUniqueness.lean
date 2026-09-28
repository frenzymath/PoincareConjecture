import PoincareConjecture.Proofs.M76.Mathlib.PlanarPLDiskUniqueness

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.subdisks_eq_of_same_rim {s q d e r : Set E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d r)
    (he : IsFinitePLBallPair (ℝ × ℝ) e r) (hds : d ⊆ s) (hes : e ⊆ s) : d = e := by
  obtain ⟨_, C, _, _, _, H, hH, _⟩ := hs
  obtain ⟨f, hf, hHf⟩ := hH
  have hfi : InjOn f s := by
    intro x hx y hy hxy
    have hxyH : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hHf ⟨x, hx⟩).trans (hxy.trans (hHf ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hxyH)
  have hfd := hd.image_of_subset hf hds hfi
  have hfe := he.image_of_subset hf hes hfi
  exact (hfi.image_eq_image_iff hds hes).mp (hfd.eq_of_same_planar_rim hfe)

end Set
