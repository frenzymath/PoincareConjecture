import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates











set_option autoImplicit false

open Set Geometry

namespace Set

variable {M E F : Type*}
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]







theorem IsFinitePLBallPair.linear_image_patch_data
    {d q : Set E} (hd : IsFinitePLBallPair M d q) (e : E ≃L[ℝ] F) :
    IsFinitePLBallPair M (e '' d) (e '' q) ∧
    (e.toHomeomorph.image d).IsFinitePL ∧
    (∀ x : d, (e.toHomeomorph.image d x : F) = e x) ∧
    (∀ (u : Set E) (x : d), (x : E) ∈ u ↔
      (e.toHomeomorph.image d x : F) ∈ e '' u) ∧
    ∀ (u : Set E) (hud : u ⊆ d) (x : u),
      e.toHomeomorph.image d ⟨x, hud x.property⟩ =
        ⟨e.toHomeomorph.image u x,
          image_mono hud (e.toHomeomorph.image u x).property⟩ := by
  have htarget : IsFinitePLBallPair M (e '' d) (e '' q) :=
    hd.affine_image e.toContinuousAffineEquiv.toContinuousAffineMap e.injective.injOn
  have hPL : (e.toHomeomorph.image d).IsFinitePL := by
    have hcopy := hd
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKd, _⟩, _⟩, _⟩ := hcopy
    exact ⟨e, ⟨K, hK, hKd,
      K.affineOnFaces_affine e.toContinuousAffineEquiv.toContinuousAffineMap⟩,
      fun _ => rfl⟩
  refine ⟨htarget, hPL, fun _ => rfl, ?_, ?_⟩
  · intro u x
    change (x : E) ∈ u ↔ e (x : E) ∈ e '' u
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, heq⟩
      simpa only [e.injective heq] using hy
  · intro u hud x
    apply Subtype.ext
    rfl

end Set
