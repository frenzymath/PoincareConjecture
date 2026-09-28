import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]



theorem IsFinitePLBallPair.model_equiv {s b : Set X}
    (hs : IsFinitePLBallPair E s b) (a : E ≃L[ℝ] F) : IsFinitePLBallPair F s b := by
  obtain ⟨hb, C, hC, hcv, hne, G, hG, hGb⟩ := hs
  obtain ⟨_, ⟨J, hJ, hJC, _⟩, _⟩ := hG.symm
  have haPL : FinitePiecewiseAffineOn a C :=
    ⟨J, hJ, hJC, J.affineOnFaces_affine a.toContinuousAffineEquiv.toContinuousAffineMap⟩
  obtain ⟨A, hA, hAval⟩ := haPL.exists_homeomorph_image a.injective.injOn
  have hane : (interior (a '' C)).Nonempty := by
    change (interior (a.toHomeomorph '' C)).Nonempty
    rw [← a.toHomeomorph.image_interior C]
    exact hne.image a
  refine ⟨hb, a '' C, hC.image a.continuous, hcv.linear_image a.toLinearMap,
    hane, G.trans A, hG.trans hA, ?_⟩
  intro x
  rw [hGb]
  change (G x : E) ∈ frontier C ↔ (A (G x) : F) ∈ frontier (a '' C)
  rw [hAval]
  change (G x : E) ∈ frontier C ↔ a.toHomeomorph (G x) ∈ frontier (a.toHomeomorph '' C)
  rw [← a.toHomeomorph.image_frontier C]
  constructor
  · exact fun hx => ⟨G x, hx, rfl⟩
  · rintro ⟨z, hz, he⟩
    exact a.injective he ▸ hz

end Set
