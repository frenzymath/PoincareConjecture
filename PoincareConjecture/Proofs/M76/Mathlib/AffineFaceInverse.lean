import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps
import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolation

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}
  {f : E → F} {g : F → E}

theorem AffineOnFaces.inverse_of_face_images (hf : K.AffineOnFaces f)
    (hleft : LeftInvOn g f K.space)
    (hfaces : ∀ t ∈ L.faces, ∃ s ∈ K.faces, f '' (s : Set E) = (t : Set F)) :
    L.AffineOnFaces g := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := hfaces t ht
  obtain ⟨a, ha⟩ := (L.indep ht).exists_continuousAffineMap_eqOn g
  obtain ⟨b, hb⟩ := hf s hs
  have hab : EqOn (a.toAffineMap.comp b.toAffineMap) (AffineMap.id ℝ E) (s : Set E) := by
    intro x hx
    change a (b x) = x
    rw [← hb (subset_convexHull ℝ _ hx)]
    exact (ha (hst ▸ mem_image_of_mem f hx)).trans (hleft (K.subset_space hs hx))
  have hab' := AffineMap.eqOn_affineSpan hab
  refine ⟨a, fun y hy => ?_⟩
  have hy' : y ∈ f '' convexHull ℝ (s : Set E) := by
    rw [hf.image_convexHull hs, hst]
    exact hy
  obtain ⟨x, hx, rfl⟩ := hy'
  have heq : a (f x) = x := by
    rw [hb hx]
    exact hab' (convexHull_subset_affineSpan _ hx)
  exact (hleft (convexHull_subset_space hs hx)).trans heq.symm

end Geometry.SimplicialComplex
