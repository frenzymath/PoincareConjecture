import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondSquareCoordinates









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_normalized_signed_tube_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N F : Set E} (S : Fin 2 → Set E)
    (H : ↥(signedTubeDiamond ×ˢ I) ≃ₜ N) (hH : H.IsFinitePL)
    (b : I → E)
    (haxis : ∀ t : I, (H ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
      (left_mem_segment ℝ _ _), t.property⟩ : E) = b t)
    (hsheet : ∀ i (x : ↥(signedTubeDiamond ×ˢ I)),
      (x : C3).1 ∈ signedTubeSheet i ↔ (H x : E) ∈ S i)
    (hfrontier : ∀ x : ↥(signedTubeDiamond ×ˢ I),
      (H x : E) ∈ F ↔ (x : C3).2 = 0 ∨ (x : C3).2 = 1) :
    ∃ τ : C3 → E,
      FinitePiecewiseAffineOn τ PolygonalCrossingResolution.tube ∧
      InjOn τ PolygonalCrossingResolution.tube ∧
      τ '' PolygonalCrossingResolution.tube = N ∧
      (∀ t : I, τ ((0, 0), t) = b t) ∧
      (∀ i z, z ∈ PolygonalCrossingResolution.tube →
        (τ z ∈ S i ↔ z.1.2 = if i = 0 then z.1.1 else -z.1.1)) ∧
      ∀ z, z ∈ PolygonalCrossingResolution.tube →
        (τ z ∈ F ↔ z.2 = 0 ∨ z.2 = 1) := by
  let map := signedSquareTubeCoordinates.trans H
  obtain ⟨τ, hτ, hval⟩ := signedSquareTubeCoordinates_isFinitePL.trans hH
  have hvalue (x : PolygonalCrossingResolution.tube) : (map x : E) = τ x := hval x
  have hinj : InjOn τ PolygonalCrossingResolution.tube := by
    intro x hx y hy he
    exact congrArg Subtype.val (map.injective (Subtype.ext
      ((hvalue ⟨x, hx⟩).trans (he.trans (hvalue ⟨y, hy⟩).symm))))
  have himage : τ '' PolygonalCrossingResolution.tube = N := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hvalue ⟨x, hx⟩]
      exact (map ⟨x, hx⟩).property
    · intro hy
      obtain ⟨x, hx⟩ := map.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (hvalue x).symm.trans (congrArg Subtype.val hx)⟩
  refine ⟨τ, hτ, hinj, himage, ?_, ?_, ?_⟩
  · intro t
    let x : PolygonalCrossingResolution.tube := ⟨((0, 0), t),
      ⟨⟨by norm_num, by norm_num⟩, t.property⟩⟩
    have hx : signedSquareTubeCoordinates x =
        ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
          (left_mem_segment ℝ _ _), t.property⟩ := Subtype.ext (signedSquareTubeCoordinates_axis t)
    exact (hvalue x).symm.trans ((congrArg (fun z => (H z : E)) hx).trans (haxis t))
  · intro i z hz
    rw [← hvalue ⟨z, hz⟩]
    change (H (signedSquareTubeCoordinates ⟨z, hz⟩) : E) ∈ S i ↔ _
    rw [← hsheet]
    exact signedSquareToDiamond_sheet z.1 hz.1 i
  · intro z hz
    rw [← hvalue ⟨z, hz⟩]
    exact hfrontier (signedSquareTubeCoordinates ⟨z, hz⟩)

end PoincareConjecture.M76.Dehn
