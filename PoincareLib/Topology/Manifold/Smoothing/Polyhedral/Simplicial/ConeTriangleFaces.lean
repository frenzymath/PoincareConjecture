import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Real.Basic

/-!
# Triangles of an actual simplicial cone

The exact erased-apex description of the constructed cone identifies
its triangles with original boundary edges. No extra triangles or
unrecorded boundary vertices are introduced.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

omit [DecidableEq E] in
/-- The apex is absent from every original boundary face when it is not
an original boundary vertex. -/
theorem apex_notMem_base_face (K : SimplicialComplex ℝ E) {c : E}
    (hc : c ∉ K.vertices) {s : Finset E} (hs : s ∈ K.faces) : c ∉ s := by
  intro hcs
  exact hc (K.down_closed hs (Finset.singleton_subset_iff.mpr hcs)
    (Finset.singleton_nonempty c))

/-- Under the exact cone face formula, the triangles are precisely the
apex joined to actual two-vertex boundary edges. -/
theorem cone_triangle_iff (K L : SimplicialComplex ℝ E) {c : E}
    (hc : c ∉ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) (t : Finset E) :
    t ∈ L.faces ∧ t.card = 3 ↔ ∃ e ∈ K.faces, e.card = 2 ∧ t = insert c e := by
  constructor
  · rintro ⟨ht, htc⟩
    have htface := (hfaces t).mp ht
    have hct : c ∈ t := by
      by_contra hct
      rw [Finset.erase_eq_of_notMem hct] at htface
      rcases htface.2 with htzero | htK
      · simp [htzero] at htc
      · have hle := hdim t htK
        omega
    have hecard : (t.erase c).card = 2 := by rw [Finset.card_erase_of_mem hct, htc]
    have heK : t.erase c ∈ K.faces := htface.2.resolve_left (by
      intro h
      simp [h] at hecard)
    exact ⟨t.erase c, heK, hecard, (Finset.insert_erase hct).symm⟩
  · rintro ⟨e, he, hec, rfl⟩
    have hce := K.apex_notMem_base_face hc he
    refine ⟨(hfaces _).mpr ⟨Finset.insert_nonempty _ _, Or.inr ?_⟩, ?_⟩
    · simpa only [Finset.erase_insert hce] using he
    · rw [Finset.card_insert_of_notMem hce, hec]

/-- Erasing the apex recovers the unique original boundary edge of an
actual cone triangle. -/
theorem existsUnique_base_edge_of_cone_triangle (K L : SimplicialComplex ℝ E) {c : E}
    (hc : c ∉ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) {t : Finset E}
    (ht : t ∈ L.faces) (htc : t.card = 3) :
    ∃! e : Finset E, e ∈ K.faces ∧ e.card = 2 ∧ t = insert c e := by
  obtain ⟨e, he, hec, hte⟩ := (K.cone_triangle_iff L hc hfaces hdim t).mp ⟨ht, htc⟩
  refine ⟨e, ⟨he, hec, hte⟩, ?_⟩
  rintro f ⟨hf, _, htf⟩
  have h := congrArg (fun s : Finset E => s.erase c) (htf.symm.trans hte)
  simpa only [Finset.erase_insert (K.apex_notMem_base_face hc hf),
    Finset.erase_insert (K.apex_notMem_base_face hc he)] using h

end Geometry.SimplicialComplex
