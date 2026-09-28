import PoincareConjecture.Proofs.M76.Mathlib.DerivedStarFaces
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)

theorem image_mem_derivedSubdivision_faces_iff [DecidableEq E]
    (a : Finset K.faces) :
    a.image c ∈ (K.derivedSubdivision c hc).faces ↔
      a.Nonempty ∧ ∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i := by
  classical
  rw [K.derivedSubdivision_faces c hc]
  constructor
  · rintro ⟨b, hb, hchain, hab⟩
    have h := Finset.image_injective (K.positiveFaceCenter_injective c hc) hab
    exact h.symm ▸ ⟨hb, hchain⟩
  · rintro ⟨ha, hchain⟩
    exact ⟨a, ha, hchain, rfl⟩

theorem derivedSubdivision_vertices_eq_range :
    (K.derivedSubdivision c hc).vertices = range c := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨a, _, _, ha⟩ := (K.derivedSubdivision_faces c hc {x}).mp hx
    have hxa : x ∈ a.image c := ha ▸ Finset.mem_singleton_self x
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hxa
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    have hs := (K.image_mem_derivedSubdivision_faces_iff c hc {s}).mpr
      ⟨Finset.singleton_nonempty _, by
        intro i hi j hj
        have hi' := Finset.mem_singleton.mp hi
        have hj' := Finset.mem_singleton.mp hj
        subst i
        subst j
        exact Or.inl le_rfl⟩
    change {c s} ∈ (K.derivedSubdivision c hc).faces
    simpa only [Finset.image_singleton] using hs

theorem ncard_derived_edge_cofaces [DecidableEq E]
    {s t : K.faces} (hst : s < t) :
    {b : Finset E | b ∈ (K.derivedSubdivision c hc).faces ∧
        b.card = 3 ∧ {c s, c t} ⊆ b}.ncard =
      {u : K.faces | u ≠ s ∧ u ≠ t ∧
        (u ≤ s ∨ s ≤ u) ∧ (u ≤ t ∨ t ≤ u)}.ncard := by
  classical
  let J := K.derivedSubdivision c hc
  let C : Set K.faces := {u | u ≠ s ∧ u ≠ t ∧
    (u ≤ s ∨ s ≤ u) ∧ (u ≤ t ∨ t ≤ u)}
  have hcinj := K.positiveFaceCenter_injective c hc
  have hcsct : c s ≠ c t := fun h => hst.ne (hcinj h)
  have himage (u : K.faces) : ({s, t, u} : Finset K.faces).image c =
      ({c s, c t} : Finset E) ∪ {c u} := by
    ext z
    simp only [Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto
  have hlink : (J.faceLink {c s, c t}).vertices = c '' C := by
    ext x
    constructor
    · intro hx
      have hxJ : x ∈ J.vertices := hx.1
      obtain ⟨u, rfl⟩ := (K.derivedSubdivision_vertices_eq_range c hc).subset hxJ
      have hnot : c u ∉ ({c s, c t} : Finset E) :=
        Finset.disjoint_singleton_right.mp hx.2.1
      have hus : u ≠ s := by
        intro h
        subst u
        exact hnot (Finset.mem_insert_self _ _)
      have hut : u ≠ t := by
        intro h
        subst u
        exact hnot (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hface : ({s, t, u} : Finset K.faces).image c ∈ J.faces := by
        rw [himage]
        exact hx.2.2
      have hchain := (K.image_mem_derivedSubdivision_faces_iff c hc _).mp hface |>.2
      exact ⟨u, ⟨hus, hut, hchain u (by simp) s (by simp),
        hchain u (by simp) t (by simp)⟩, rfl⟩
    · rintro ⟨u, ⟨hus, hut, hsu, htu⟩, rfl⟩
      refine ⟨?_, Finset.disjoint_singleton_right.mpr ?_, ?_⟩
      · exact (K.derivedSubdivision_vertices_eq_range c hc).superset ⟨u, rfl⟩
      · intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hus (hcinj h)
        · exact hut (hcinj (Finset.mem_singleton.mp h))
      · have hface : ({s, t, u} : Finset K.faces).image c ∈ J.faces := by
          apply (K.image_mem_derivedSubdivision_faces_iff c hc _).mpr
          refine ⟨Finset.insert_nonempty _ _, ?_⟩
          intro i hi j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
          rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
          · exact Or.inl le_rfl
          · exact Or.inl hst.le
          · exact hsu.symm
          · exact Or.inr hst.le
          · exact Or.inl le_rfl
          · exact htu.symm
          · exact hsu
          · exact htu
          · exact Or.inl le_rfl
        rwa [himage] at hface
  have hcount := J.ncard_faceLink_vertices_eq_cofaces {c s, c t}
  rw [Finset.card_pair hcsct] at hcount
  rw [← hcount, hlink, ncard_image_of_injective _ hcinj]

end Geometry.SimplicialComplex
