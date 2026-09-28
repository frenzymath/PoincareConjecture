import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLTransport
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem IsFinitePL.exists_model_of_ambient_image {s : Set E} {t : Set F}
    {e : s ≃ₜ t} (he : e.IsFinitePL) (H : E ≃ₜ E)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space) :
    ∃ g : (H '' s : Set E) ≃ₜ t, g.IsFinitePL := by
  have hcopy := he
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hcopy
  have hHs := hH K hK
  rw [hKs] at hHs
  obtain ⟨F, hF, _⟩ := hHs.exists_homeomorph_image H.injective.injOn
  exact ⟨F.symm.trans e, hF.symm.trans he⟩

end Homeomorph

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePLBallPair.exists_sphere_model_of_deformed_disk_union
    {s d b : Set E} (hs : IsFinitePLBallPair (ℝ × ℝ) s b)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hmeet : s ∩ d = b)
    (H : E ≃ₜ E) (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space) :
    ∃ g : (H '' (s ∪ d) : Set E) ≃ₜ frontier (TriangularRoofModel.halfBall 1),
      g.IsFinitePL := by
  obtain ⟨e, he, _⟩ := hs.exists_sphere_model_of_disk_union hd hmeet
  exact he.exists_model_of_ambient_image H hH

end Set
