import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcJointRestrictions

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_signed_diamond_radius_restriction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s r : Set E} (G : signedTubeDiamond ≃ₜ s) (hG : G.IsFinitePL)
    (i : Fin 2) (sign : Bool) (hr : r ⊆ s)
    (hmem : ∀ x : signedTubeDiamond,
      (x : ℝ × ℝ) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ r) :
    ∃ e : signedTubeRadius i sign ≃ₜ r, e.IsFinitePL ∧
      ∀ x, (e x : E) = G ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ := by
  let e := G.restrictSubsets (signedTubeRadius_subset_diamond i sign) hr hmem
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := signedTube_radius_ball i sign
  exact ⟨e, hG.restrictSubsets (signedTubeRadius_subset_diamond i sign) hr hmem K hK hKs,
    fun _ => rfl⟩

end PoincareConjecture.M76.Dehn
