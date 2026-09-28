import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}





theorem AffineOnFaces.face_card_le_two_of_line
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    {s : Finset E} (hs : s ∈ K.faces) (v : F)
    (hline : ∀ x ∈ s, ∃ r : ℝ, f x = r • v) : s.card ≤ 2 := by
  classical
  have hind : AffineIndependent ℝ ((↑) : (s.image f) → F) := by
    change AffineIndependent ℝ ((↑) : ↥((s.image f : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact hf.affineIndependent_image_face hinj hs
  have hspan : (s.image f : Set F) ⊆
      (affineSpan ℝ (({0, v} : Finset F) : Set F) : Set F) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨r, hr⟩ := hline x hx
    rw [hr]
    rw [Finset.coe_pair]
    change r • v ∈ affineSpan ℝ ({0, v} : Set F)
    simpa only [AffineMap.lineMap_apply_module,
      smul_zero, zero_add] using AffineMap.lineMap_mem_affineSpan_pair r (0 : F) v
  have hinjs : InjOn f (s : Set E) :=
    hinj.mono ((subset_convexHull ℝ _).trans (K.convexHull_subset_space hs))
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinjs).symm
    _ ≤ ({0, v} : Finset F).card := hind.card_le_card_of_subset_affineSpan hspan
    _ ≤ 2 := by
      calc
        ({0, v} : Finset F).card ≤ ({v} : Finset F).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp

end Geometry.SimplicialComplex
