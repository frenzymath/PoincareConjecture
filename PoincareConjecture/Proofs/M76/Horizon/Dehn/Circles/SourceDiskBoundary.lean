import PoincareConjecture.Proofs.M76.Mathlib.NestedPLBallBoundary

set_option autoImplicit false

open Set Geometry

namespace Dehn

theorem finitePL_ball_homeomorph_boundary
    {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {S B : Set E} {T C : Set F}
    (hS : IsFinitePLBallPair V S B) (hT : IsFinitePLBallPair V T C)
    (H : S ≃ₜ T) (hH : H.IsFinitePL) (x : S) :
    (H x : F) ∈ C ↔ (x : E) ∈ B := by
  obtain ⟨f, hf, hfval⟩ := hH
  have hi : InjOn f S := by
    intro y hy z hz he
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hfval ⟨y, hy⟩).trans (he.trans (hfval ⟨z, hz⟩).symm))))
  have him : f '' S = T := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hfval ⟨z, hz⟩]
      exact (H ⟨z, hz⟩).property
    · intro hy
      exact ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property,
        (hfval _).symm.trans (congrArg Subtype.val (H.apply_symm_apply _))⟩
  have hb := hS.image hf hi
  rw [him] at hb
  have hboundary : f '' B = C := hb.boundary_eq_of_same_carrier hT
  rw [hfval, ← hboundary]
  constructor
  · rintro ⟨y, hy, he⟩
    exact hi (hS.1 hy) x.property he ▸ hy
  · intro hx
    exact mem_image_of_mem f hx

end Dehn
