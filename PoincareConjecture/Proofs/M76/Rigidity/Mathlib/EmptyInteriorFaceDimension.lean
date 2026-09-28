import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedFaceDimension
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem face_card_le_of_interior_space_eq_empty
    (K : SimplicialComplex ℝ E) (hint : interior K.space = ∅)
    {s : Finset E} (hs : s ∈ K.faces) : s.card ≤ Module.finrank ℝ E := by
  have hle : s.card ≤ Module.finrank ℝ E + 1 := by
    simpa only [Fintype.card_coe] using
      (K.indep hs).card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  by_contra hnot
  have hcard : s.card = Module.finrank ℝ E + 1 := by omega
  let b := (K.indep hs).affineBasisOfCard hcard
  have hnonempty : (interior (convexHull ℝ (s : Set E))).Nonempty := by
    apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    simpa [b] using b.tot
  obtain ⟨x, hx⟩ := hnonempty
  exact Set.notMem_empty x (hint ▸ interior_mono (K.convexHull_subset_space hs) hx)



theorem AffineOnFaces.face_card_le_of_injOn_of_empty_interior
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {K : SimplicialComplex ℝ E} {f : E → F}
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    (hint : interior (f '' K.space) = ∅)
    {s : Finset E} (hs : s ∈ K.faces) : s.card ≤ Module.finrank ℝ F := by
  classical
  let L := hf.embeddedImage hi
  have hsL : s.image f ∈ L.faces :=
    (hf.image_mem_embeddedImage_iff hi (K.subset_space hs)).mpr hs
  have hLint : interior L.space = ∅ := by
    rw [hf.embeddedImage_space]
    exact hint
  have hcard := L.face_card_le_of_interior_space_eq_empty hLint hsL
  have himage : (s.image f).card = s.card :=
    Finset.card_image_iff.mpr (hi.mono (K.subset_space hs))
  simpa only [himage] using hcard

end Geometry.SimplicialComplex
