import PoincareConjecture.Proofs.M76.Mathlib.DerivedFaceChainIncidence

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)

theorem derivedSubdivision_link_faces {p : E} (hp : {p} ∈ K.faces) (f : Finset E) :
    f ∈ ((K.derivedSubdivision c hc).link p).faces ↔
      ∃ a : Finset (K.link p).faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧
        f = a.image (fun s => c ⟨insert p s.val, s.property.2.2⟩) := by
  classical
  let d : (K.link p).faces → E := fun s => c ⟨insert p s.val, s.property.2.2⟩
  have hcp : c ⟨{p}, hp⟩ = p := K.positiveFaceCenter_singleton c hc hp
  constructor
  · intro hf
    obtain ⟨b, hb, hchain, hfb, hall⟩ :=
      (K.derivedSubdivision_closedStar_faces c hc hp f).mp ⟨hf.1, hf.2.2⟩
    have herase (i : K.faces) (hi : i ∈ b) : i.val.erase p ∈ (K.link p).faces := by
      have hnot : i.val ≠ {p} := by
        intro h
        apply hf.2.1
        rw [hfb]
        exact Finset.mem_image.mpr ⟨i, hi,
          (congrArg c (show i = ⟨{p}, hp⟩ from Subtype.ext h)).trans hcp⟩
      have hne : (i.val.erase p).Nonempty := by
        by_contra h
        have he := Finset.not_nonempty_iff_eq_empty.mp h
        apply hnot
        rw [← Finset.insert_erase (hall i hi), he]
        rfl
      refine ⟨K.down_closed i.property (Finset.erase_subset _ _) hne,
        Finset.notMem_erase _ _, ?_⟩
      simpa only [Finset.insert_erase (hall i hi)] using i.property
    let er : b → (K.link p).faces := fun i => ⟨i.val.val.erase p, herase i.val i.property⟩
    have hcenter (i : b) : d (er i) = c i.val := by
      apply congrArg c
      apply Subtype.ext
      exact Finset.insert_erase (hall i.val i.property)
    refine ⟨b.attach.image er, hb.attach.image er, ?_, ?_⟩
    · intro i hi j hj
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
      rcases hchain u.val u.property v.val v.property with h | h
      · exact Or.inl (Finset.erase_subset_erase p h)
      · exact Or.inr (Finset.erase_subset_erase p h)
    · change f = (b.attach.image er).image d
      rw [hfb]
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
        refine Finset.mem_image.mpr ⟨er ⟨i, hi⟩,
          Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
        exact (hcenter ⟨i, hi⟩).trans hix
      · intro hx
        obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_image.mpr ⟨i.val, i.property, (hcenter i).symm.trans hjx⟩
  · rintro ⟨a, ha, hchain, rfl⟩
    let ins : (K.link p).faces → K.faces := fun i => ⟨insert p i.val, i.property.2.2⟩
    have hstar : a.image d ∈ ((K.derivedSubdivision c hc).closedStar p).faces := by
      apply (K.derivedSubdivision_closedStar_faces c hc hp _).mpr
      refine ⟨a.image ins, ha.image ins, ?_, ?_, ?_⟩
      · intro i hi j hj
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
        rcases hchain u hu v hv with h | h
        · exact Or.inl (Finset.insert_subset_insert p h)
        · exact Or.inr (Finset.insert_subset_insert p h)
      · rw [Finset.image_image]
        rfl
      · intro i hi
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_insert_self _ _
    refine ⟨hstar.1, ?_, hstar.2⟩
    intro h
    obtain ⟨i, _, hip⟩ := Finset.mem_image.mp h
    have heq : insert p i.val = {p} :=
      congrArg Subtype.val ((K.positiveFaceCenter_injective c hc) (hip.trans hcp.symm))
    obtain ⟨q, hq⟩ := (K.link p).nonempty_of_mem_faces i.property
    have hqp : q = p := Finset.mem_singleton.mp
      (heq ▸ Finset.mem_insert_of_mem hq)
    exact i.property.2.1 (hqp ▸ hq)

end Geometry.SimplicialComplex
