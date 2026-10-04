import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionPLTransport
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.PLDiskSurgeryModels

/-!
# Actual finite PL models after supported sphere deformation

Universal finite-polyhedron regularity transports a finite PL
model to the literal ambient image. The capped-disk specialization
constructs both image disks and uses their exact shared rim.
See Alexander 1924, pp. 7--8 and M76 derivation 260.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite PL model transports through an ambient map
whose finite-polyhedron certificates are universal. Its inverse
gives a model for the literal image carrier. See Alexander
pp. 7--8 and derivation 260. -/
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

/-- The literal deformed capped disk is a finite PL sphere.
Both image disk pairs and their entire shared rim are constructed
from the original cut and the same ambient map. This asserts a
sphere model, not an ambient ball filling. See Alexander
pp. 7--8 and derivation 260. -/
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
