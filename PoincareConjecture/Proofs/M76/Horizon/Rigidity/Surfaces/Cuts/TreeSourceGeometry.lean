import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.BoundaryInventory










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E)

theorem exists_triangle_apex_over_edge (s : Triangle K) {a b : E}
    (hab : a ≠ b) (hsub : ({a, b} : Finset E) ⊆ s.val) :
    ∃ d : E, s.val = {a, d, b} ∧ AffineIndependent ℝ ![a, d, b] := by
  have hlt : ({a, b} : Finset E).card < s.val.card := by
    rw [Finset.card_pair hab, s.property.2]
    omega
  obtain ⟨d, hd, hdn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hda : d ≠ a := fun h => hdn (by simp [h])
  have hdb : d ≠ b := fun h => hdn (by simp [h])
  have hfull : ({a, d, b} : Finset E) = s.val := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hsub (by simp)
      · exact hd
      · exact hsub (by simp)
    · simp [s.property.2, hab, hda.symm, hdb]
  have hinj : Function.Injective (![a, d, b] : Fin 3 → E) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hrange : range (![a, d, b] : Fin 3 → E) = (s.val : Set E) := by
    rw [← hfull]
    ext x
    simp [eq_comm, or_comm, or_left_comm]
  exact ⟨d, hfull.symm,
    ((K.indep s.property.1).mono hrange.subset).of_set_of_injective hinj⟩

theorem original_triangle_inter_eq_shared_edge
    {s t : Triangle K} (hne : s ≠ t) {e : Finset E}
    (he : e.card = 2) (hes : e ⊆ s.val) (het : e ⊆ t.val) :
    s.val ∩ t.val = e := by
  have hsc := s.property.2
  have htc := t.property.2
  have hneinter : s.val ∩ t.val ≠ s.val := by
    intro h
    apply hne
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le (h ▸ Finset.inter_subset_right) (by omega)
  have hhi := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hneinter⟩)
  exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hes het) (by omega)).symm

theorem original_triangle_hulls_inter_eq_shared_segment
    {s t : Triangle K} (hne : s ≠ t) {a b : E} (hab : a ≠ b)
    (hes : ({a, b} : Finset E) ⊆ s.val) (het : ({a, b} : Finset E) ⊆ t.val) :
    convexHull ℝ (s.val : Set E) ∩ convexHull ℝ (t.val : Set E) = segment ℝ a b := by
  rw [K.convexHull_inter_convexHull s.property.1 t.property.1,
    ← Finset.coe_inter, original_triangle_inter_eq_shared_edge K hne
      (Finset.card_pair hab) hes het, Finset.coe_pair, convexHull_pair]

theorem two_cofaces_inventory {e : Finset E}
    (hcount : {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    {s t : Triangle K} (hne : s ≠ t) (hes : e ⊆ s.val) (het : e ⊆ t.val) :
    ∀ u : Triangle K, e ⊆ u.val ↔ u = s ∨ u = t := by
  obtain ⟨a, b, hab, hinv⟩ := Set.ncard_eq_two.mp hcount
  have hs : s.val = a ∨ s.val = b := by
    have hmem : s.val ∈ {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t} :=
      ⟨s.property.1, s.property.2, hes⟩
    rwa [hinv] at hmem
  have ht : t.val = a ∨ t.val = b := by
    have hmem : t.val ∈ {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t} :=
      ⟨t.property.1, t.property.2, het⟩
    rwa [hinv] at hmem
  intro u
  constructor
  · intro heu
    have hu : u.val = a ∨ u.val = b := by
      have hmem : u.val ∈ {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t} :=
        ⟨u.property.1, u.property.2, heu⟩
      rwa [hinv] at hmem
    rcases hs with hs | hs <;> rcases ht with ht | ht <;> rcases hu with hu | hu
    all_goals first
      | exact Or.inl (Subtype.ext (hu.trans hs.symm))
      | exact Or.inr (Subtype.ext (hu.trans ht.symm))
      | exact (hne (Subtype.ext (hs.trans ht.symm))).elim
  · rintro (rfl | rfl)
    · exact hes
    · exact het

end PoincareConjecture.M76.OriginalTriangleCopies
