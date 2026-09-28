import PoincareConjecture.Proofs.M76.Mathlib.DerivedSubdivisionRestriction
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceSpan
import PoincareConjecture.Proofs.M76.Mathlib.DirectedSimplicialUnion
import Mathlib.Order.Interval.Finset.Nat










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]





theorem exists_derived_subdivision (K : SimplicialComplex ℝ E) (c : Finset E → E)
    (hc : ∀ s ∈ K.faces, ∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧
      (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = c s) :
    ∃ D : SimplicialComplex ℝ E, D.IsSubdivision K ∧
      ∀ t : Finset E, t ∈ D.faces ↔
        ∃ a : Finset (Finset E), a.Nonempty ∧ (∀ s ∈ a, s ∈ K.faces) ∧
          (∀ s ∈ a, ∀ u ∈ a, s ⊆ u ∨ u ⊆ s) ∧ t = a.image c := by
  classical
  let L (A : Finset K.faces) : SimplicialComplex ℝ E := by
    let : Fintype (K.finiteFaceSpan A).faces := (K.finiteFaceSpan_finite A).fintype
    exact (K.finiteFaceSpan A).derivedSubdivision (fun s => c s.val)
      (fun s => hc s.val (K.finiteFaceSpan_le A s.property))
  have hLA (A : Finset K.faces) : (L A).IsSubdivision (K.finiteFaceSpan A) := by
    let : Fintype (K.finiteFaceSpan A).faces := (K.finiteFaceSpan_finite A).fintype
    exact (K.finiteFaceSpan A).derivedSubdivision_isSubdivision (fun s => c s.val)
      (fun s => hc s.val (K.finiteFaceSpan_le A s.property))
  have hLfaces (A : Finset K.faces) (t : Finset E) :
      t ∈ (L A).faces ↔ ∃ a : Finset (Finset E), a.Nonempty ∧
        (∀ s ∈ a, s ∈ (K.finiteFaceSpan A).faces) ∧
        (∀ s ∈ a, ∀ u ∈ a, s ⊆ u ∨ u ⊆ s) ∧ t = a.image c := by
    let : Fintype (K.finiteFaceSpan A).faces := (K.finiteFaceSpan_finite A).fintype
    exact (K.finiteFaceSpan A).derivedSubdivision_faces_of_ambient_centers c
      (fun s hs => hc s (K.finiteFaceSpan_le A hs)) t
  have hmono : Monotone L := by
    intro A B hAB
    let : Fintype (K.finiteFaceSpan A).faces := (K.finiteFaceSpan_finite A).fintype
    let : Fintype (K.finiteFaceSpan B).faces := (K.finiteFaceSpan_finite B).fintype
    exact (K.finiteFaceSpan A).derivedSubdivision_mono (K.finiteFaceSpan_mono hAB) c
      (fun s hs => hc s (K.finiteFaceSpan_le B hs))
  have hdir : Directed (· ≤ ·) L := fun A B =>
    ⟨A ∪ B, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  let D := directedUnion L hdir
  have hspace : D.space = K.space := by
    change (directedUnion L hdir).space = K.space
    rw [directedUnion_space]
    calc
      (⋃ A, (L A).space) = ⋃ A, (K.finiteFaceSpan A).space :=
        iUnion_congr fun A => (hLA A).space_eq
      _ = K.space := K.iUnion_finiteFaceSpan_space
  refine ⟨D, ⟨hspace, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨A, hA⟩ := mem_iUnion.mp ht
    obtain ⟨s, hs, hts⟩ := (hLA A).face_subset t hA
    exact ⟨s, K.finiteFaceSpan_le A hs, hts⟩
  · intro t
    constructor
    · intro ht
      obtain ⟨A, hA⟩ := mem_iUnion.mp ht
      obtain ⟨a, ha, hfaces, hchain, he⟩ := (hLfaces A t).mp hA
      exact ⟨a, ha, fun s hs => K.finiteFaceSpan_le A (hfaces s hs), hchain, he⟩
    · rintro ⟨a, ha, hfaces, hchain, rfl⟩
      let v : a → K.faces := fun s => ⟨s.val, hfaces s.val s.property⟩
      let A := a.attach.image v
      apply mem_iUnion.mpr
      refine ⟨A, (hLfaces A (a.image c)).mpr ⟨a, ha, ?_, hchain, rfl⟩⟩
      intro s hs
      apply (K.finiteFaceSpan_faces A s).mpr
      refine ⟨K.nonempty_of_mem_faces (hfaces s hs), v ⟨s, hs⟩, ?_, Finset.Subset.refl s⟩
      exact Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach a ⟨s, hs⟩, rfl⟩




theorem center_chain_faces_card_le {K D : SimplicialComplex ℝ E} {c : Finset E → E}
    (hD : ∀ t ∈ D.faces, ∃ a : Finset (Finset E), a.Nonempty ∧
      (∀ s ∈ a, s ∈ K.faces) ∧ (∀ s ∈ a, ∀ u ∈ a, s ⊆ u ∨ u ⊆ s) ∧ t = a.image c)
    {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1) :
    ∀ t ∈ D.faces, t.card ≤ N + 1 := by
  classical
  intro t ht
  obtain ⟨a, _, hfaces, hchain, rfl⟩ := hD t ht
  have hcard : a.card ≤ (Finset.Icc 1 (N + 1)).card := by
    apply Finset.card_le_card_of_injOn Finset.card
    · intro s hs
      exact Finset.mem_Icc.mpr
        ⟨(K.nonempty_of_mem_faces (hfaces s hs)).card_pos, hN s (hfaces s hs)⟩
    · intro s hs u hu he
      rcases hchain s hs u hu with h | h
      · exact Finset.eq_of_subset_of_card_le h he.ge
      · exact (Finset.eq_of_subset_of_card_le h he.le).symm
  exact Finset.card_image_le.trans (by simpa using hcard)

end Geometry.SimplicialComplex
