import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageIncidence
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}

theorem AffineOnFaces.face_card_le_of_injOn [FiniteDimensional ℝ F]
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    {s : Finset E} (hs : s ∈ K.faces) :
    s.card ≤ Module.finrank ℝ F + 1 := by
  classical
  let L := hf.embeddedImage hi
  have hsL : s.image f ∈ L.faces :=
    (hf.image_mem_embeddedImage_iff hi (K.subset_space hs)).mpr hs
  have hcard := (L.indep hsL).card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have himage : (s.image f).card = s.card :=
    Finset.card_image_iff.mpr (hi.mono (K.subset_space hs))
  simpa only [Fintype.card_coe, himage] using hcard

theorem AffineOnFaces.pullback_embeddedImage_coface [DecidableEq F]
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    {t : Finset F} (ht : t ∈ (hf.embeddedImage hi).faces)
    (hst : s.image f ⊆ t) {n : ℕ} (htcard : t.card = n) :
    ∃ u ∈ K.faces, s ⊆ u ∧ u.card = n ∧ u.image f = t := by
  rw [hf.embeddedImage_faces] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  refine ⟨u, hu, ?_, ?_, rfl⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ :=
      Finset.mem_image.mp (hst (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    exact hi (K.subset_space hu hy) (K.subset_space hs hx) hyx ▸ hy
  · exact (Finset.card_image_iff.mpr (hi.mono (K.subset_space hu))).symm.trans htcard

end Geometry.SimplicialComplex
