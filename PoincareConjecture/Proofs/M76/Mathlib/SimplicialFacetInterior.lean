import PoincareConjecture.Proofs.M76.Mathlib.FullSimplexBasis
import PoincareConjecture.Proofs.M76.Mathlib.SimplexOppositeApices
import PoincareConjecture.Proofs.M76.Mathlib.SimplexRelativeInteriorCoordinates
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem mem_interior_space_of_full_face (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = Module.finrank ℝ E + 1)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    x ∈ interior K.space := by
  let b := (K.indep hs).affineBasisOfCard hcard
  have h : x ∈ interior (convexHull ℝ (range b)) :=
    b.mem_interior_convexHull_of_mem_intrinsicInterior (by simpa [b] using hx)
  exact interior_mono (by simpa [b] using K.convexHull_subset_space hs) h

theorem mem_interior_union_of_paired_facet (K : SimplicialComplex ℝ E)
    {f t u : Finset E} (hfcard : f.card = Module.finrank ℝ E)
    (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (htcard : t.card = Module.finrank ℝ E + 1)
    (hucard : u.card = Module.finrank ℝ E + 1)
    (hft : f ⊆ t) (hfu : f ⊆ u) (htu : t ≠ u)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (f : Set E))) :
    x ∈ interior (convexHull ℝ (t : Set E) ∪ convexHull ℝ (u : Set E)) := by
  classical
  obtain ⟨p, hpf, hpt⟩ := Finset.exists_eq_insert_iff.mpr
    (And.intro hft (show f.card + 1 = t.card by omega))
  obtain ⟨q, hqf, hqu⟩ := Finset.exists_eq_insert_iff.mpr
    (And.intro hfu (show f.card + 1 = u.card by omega))
  have hpq : p ≠ q := by
    intro he
    apply htu
    rw [← hpt, ← hqu, he]
  have hpmem : p ∈ t := by rw [← hpt]; exact Finset.mem_insert_self p f
  let i : t := ⟨p, hpmem⟩
  let b := (K.indep ht).affineBasisOfCard htcard
  have hfimage : b '' {j : t | j ≠ i} = (f : Set E) := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      change (j : E) ∈ f
      have hjp : (j : E) ≠ p := fun he => hj (Subtype.ext he)
      have hjt := (Finset.ext_iff.mp hpt (j : E)).mpr j.property
      exact (Finset.mem_insert.mp hjt).resolve_left hjp
    · intro hy
      refine ⟨⟨y, hft hy⟩, ?_, rfl⟩
      intro he
      have he' : y = p := congrArg Subtype.val he
      exact hpf (he' ▸ (show y ∈ f from hy))
  have hrange : range b = (t : Set E) := (K.indep ht).range_affineBasisOfCard htcard
  have hrangeq : range (Function.update b i q) = (u : Set E) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hji : j = i
      · subst j
        rw [Function.update_self, ← hqu]
        exact Finset.mem_insert_self q f
      · rw [Function.update_of_ne hji]
        have hjf : b j ∈ (f : Set E) := by
          rw [← hfimage]
          exact mem_image_of_mem b hji
        exact hfu hjf
    · intro hy
      rw [← hqu] at hy
      rcases Finset.mem_insert.mp hy with he | hyf
      · exact ⟨i, by simpa only [Function.update_self] using he.symm⟩
      · change y ∈ (f : Set E) at hyf
        rw [← hfimage] at hyf
        obtain ⟨j, hj, rfl⟩ := hyf
        exact ⟨j, Function.update_of_ne hj q b⟩
  have hfull : affineSpan ℝ (range (Function.update b i q)) = ⊤ := by
    rw [hrangeq]
    simpa using ((K.indep hu).affineBasisOfCard hucard).tot
  have hximage : x ∈ intrinsicInterior ℝ (convexHull ℝ (b '' {j : t | j ≠ i})) := by
    rw [hfimage]
    exact hx
  have hxi : b.coord i x = 0 := b.coord_eq_zero_of_mem_affineSpan_image
    (s := {j : t | j ≠ i}) (by simp)
    (convexHull_subset_affineSpan _ (intrinsicInterior_subset hximage))
  have hxpos : ∀ j, j ≠ i → 0 < b.coord j x := fun j hj =>
    b.coord_pos_of_mem_intrinsicInterior_convexHull_image hximage hj
  have htuinter : t ∩ u = f := by
    ext y
    simp only [← hpt, ← hqu, Finset.mem_inter, Finset.mem_insert]
    aesop
  have hinter : ∀ y ∈ convexHull ℝ (range b) ∩
      convexHull ℝ (range (Function.update b i q)), b.coord i y = 0 := by
    intro y hy
    rw [hrange, hrangeq] at hy
    have hyf := K.inter_subset_convexHull ht hu hy
    rw [← Finset.coe_inter, htuinter, ← hfimage] at hyf
    exact b.coord_eq_zero_of_mem_affineSpan_image (s := {j : t | j ≠ i}) (by simp)
      (convexHull_subset_affineSpan _ hyf)
  have hxint := b.mem_interior_union_of_common_facet_intersection i q x hfull hxi hxpos hinter
  rw [hrange, hrangeq] at hxint
  exact hxint

theorem mem_interior_space_of_paired_facet (K : SimplicialComplex ℝ E)
    {f t u : Finset E} (hfcard : f.card = Module.finrank ℝ E)
    (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (htcard : t.card = Module.finrank ℝ E + 1)
    (hucard : u.card = Module.finrank ℝ E + 1)
    (hft : f ⊆ t) (hfu : f ⊆ u) (htu : t ≠ u)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (f : Set E))) :
    x ∈ interior K.space :=
  interior_mono (union_subset (K.convexHull_subset_space ht)
    (K.convexHull_subset_space hu))
      (K.mem_interior_union_of_paired_facet hfcard ht hu htcard hucard hft hfu htu hx)

end Geometry.SimplicialComplex
