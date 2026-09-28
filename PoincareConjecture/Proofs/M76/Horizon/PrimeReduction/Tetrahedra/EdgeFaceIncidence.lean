import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeMarks









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_two_triangle_cofaces_of_tetrahedron
    {E : Type*} [DecidableEq E] {a t : Finset E}
    (hat : a ⊆ t) (ha : a.card = 2) (ht : t.card = 4) :
    ∃ s u : Finset E, s ≠ u ∧ a ⊆ s ∧ a ⊆ u ∧
      s ⊆ t ∧ u ⊆ t ∧ s.card = 3 ∧ u.card = 3 ∧
      ∀ b : Finset E, b ⊆ t → b.card = 3 → (a ⊆ b ↔ b = s ∨ b = u) := by
  have hdiff : (t \ a).card = 2 := by
    rw [Finset.card_sdiff_of_subset hat, ht, ha]
  obtain ⟨v, w, hvw, hpair⟩ := Finset.card_eq_two.mp hdiff
  have hv : v ∈ t \ a := hpair.symm ▸ (by simp)
  have hw : w ∈ t \ a := hpair.symm ▸ (by simp)
  have hvT := (Finset.mem_sdiff.mp hv).1
  have hvA := (Finset.mem_sdiff.mp hv).2
  have hwT := (Finset.mem_sdiff.mp hw).1
  have hwA := (Finset.mem_sdiff.mp hw).2
  refine ⟨insert v a, insert w a, ?_, Finset.subset_insert _ _,
    Finset.subset_insert _ _, Finset.insert_subset hvT hat,
    Finset.insert_subset hwT hat, ?_, ?_, ?_⟩
  · intro heq
    have h : v ∈ insert w a := heq ▸ Finset.mem_insert_self v a
    exact (Finset.mem_insert.mp h).elim hvw hvA
  · simp [hvA, ha]
  · simp [hwA, ha]
  · intro b hbt hb
    constructor
    · intro hab
      have hba : (b \ a).card = 1 := by
        rw [Finset.card_sdiff_of_subset hab, hb, ha]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hba
      have hzba : z ∈ b \ a := hz.symm ▸ (by simp)
      have hzt : z ∈ t \ a := Finset.mem_sdiff.mpr
        ⟨hbt (Finset.mem_sdiff.mp hzba).1, (Finset.mem_sdiff.mp hzba).2⟩
      have hbz : b = insert z a := by
        ext x
        constructor
        · intro hxb
          by_cases hxa : x ∈ a
          · exact Finset.mem_insert_of_mem hxa
          · have hxd : x ∈ b \ a := Finset.mem_sdiff.mpr ⟨hxb, hxa⟩
            rw [hz] at hxd
            exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hxd))
        · intro hx
          rcases Finset.mem_insert.mp hx with rfl | hxa
          · exact (Finset.mem_sdiff.mp hzba).1
          · exact hab hxa
      rw [hpair] at hzt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzt
      rcases hzt with rfl | rfl
      · exact Or.inl hbz
      · exact Or.inr hbz
    · rintro (rfl | rfl) <;> exact Finset.subset_insert _ _

theorem exists_two_physical_triangle_cofaces_at_edge_point
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {a t : Finset E} (haK : a ∈ K.faces) (htK : t ∈ K.faces)
    (hat : a ⊆ t) (ha : a.card = 2) (ht : t.card = 4)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E))) :
    ∃ s u : Finset E, s ≠ u ∧ s ∈ K.faces ∧ u ∈ K.faces ∧
      a ⊆ s ∧ a ⊆ u ∧ s ⊆ t ∧ u ⊆ t ∧ s.card = 3 ∧ u.card = 3 ∧
      ∀ b : Finset E, b ⊆ t → b.card = 3 →
        (g x ∈ g '' convexHull ℝ (b : Set E) ↔ b = s ∨ b = u) := by
  obtain ⟨s, u, hsu, has, hau, hst, hut, hs, hu, hfaces⟩ :=
    exists_two_triangle_cofaces_of_tetrahedron hat ha ht
  have hsK : s ∈ K.faces := K.down_closed htK hst (Finset.card_pos.mp (by omega))
  have huK : u ∈ K.faces := K.down_closed htK hut (Finset.card_pos.mp (by omega))
  refine ⟨s, u, hsu, hsK, huK, has, hau, hst, hut, hs, hu, ?_⟩
  intro b hbt hb
  have hbK : b ∈ K.faces := K.down_closed htK hbt (Finset.card_pos.mp (by omega))
  rw [← hfaces b hbt hb]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hyx : y = x := hgi (K.convexHull_subset_space hbK hy)
      (K.convexHull_subset_space haK (intrinsicInterior_subset hx)) heq
    exact K.subset_of_mem_intrinsicInterior_face haK hbK hx (hyx ▸ hy)
  · intro hab
    exact mem_image_of_mem g (convexHull_mono hab (intrinsicInterior_subset hx))

end PoincareConjecture.M76
