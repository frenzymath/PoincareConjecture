import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.ConeTriangleFaces









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem cone_edge_iff (K L : SimplicialComplex ℝ E) {c : E}
    (hc : c ∉ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (s : Finset E) :
    s ∈ L.faces ∧ s.card = 2 ↔
      (s ∈ K.faces ∧ s.card = 2) ∨ ∃ q ∈ K.vertices, s = {c, q} := by
  constructor
  · rintro ⟨hs, hcard⟩
    have hf := (hfaces s).mp hs
    by_cases hcs : c ∈ s
    · have hecard : (s.erase c).card = 1 := by rw [Finset.card_erase_of_mem hcs, hcard]
      have heK : s.erase c ∈ K.faces := hf.2.resolve_left (by
        intro h
        simp [h] at hecard)
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hecard
      refine Or.inr ⟨q, ?_, ?_⟩
      · change ({q} : Finset E) ∈ K.faces
        rwa [← hq]
      · rw [← Finset.insert_erase hcs, hq]
    · rw [Finset.erase_eq_of_notMem hcs] at hf
      exact Or.inl ⟨hf.2.resolve_left (fun h => by simp [h] at hcard), hcard⟩
  · rintro (⟨hs, hcard⟩ | ⟨q, hq, rfl⟩)
    · refine ⟨(hfaces s).mpr ⟨K.nonempty_of_mem_faces hs, Or.inr ?_⟩, hcard⟩
      rwa [Finset.erase_eq_of_notMem (K.apex_notMem_base_face hc hs)]
    · have hcq : c ≠ q := fun h => hc (h.symm ▸ hq)
      refine ⟨(hfaces _).mpr ⟨by simp, Or.inr ?_⟩, Finset.card_pair hcq⟩
      simpa [hcq, Ne.symm hcq] using (show ({q} : Finset E) ∈ K.faces from hq)



theorem cone_edge_has_unmarked_vertex (K L : SimplicialComplex ℝ E) {c : E}
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (Z : Set E) (hc : c ∉ Z)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 → ∃ q ∈ s, q ∉ Z) :
    ∀ s ∈ L.faces, s.card = 2 → ∃ q ∈ s, q ∉ Z := by
  intro s hs hcard
  by_cases hcs : c ∈ s
  · exact ⟨c, hcs, hc⟩
  · have hf := (hfaces s).mp hs
    rw [Finset.erase_eq_of_notMem hcs] at hf
    exact hboundary s (hf.2.resolve_left (fun h => by simp [h] at hcard)) hcard

end Geometry.SimplicialComplex
