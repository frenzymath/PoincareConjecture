import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalSliceSegments

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

def exceptionalOriginalVertices (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (q : E) : Option (K.strictCrossingEdges A) → Finset E
  | none => {q}
  | some e => e.val

theorem exceptionalSliceGraph_adj_some_iff (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (q : E) (e : K.strictCrossingEdges A)
    (v : Option (K.strictCrossingEdges A)) :
    (K.exceptionalSliceGraph A q).Adj (some e) v ↔
      e.val ∪ K.exceptionalOriginalVertices A q v ∈ K.faces ∧
        (e.val ∪ K.exceptionalOriginalVertices A q v).card = 3 := by
  cases v with
  | none =>
    change (insert q e.val ∈ K.faces ∧ (insert q e.val).card = 3) ↔
      (e.val ∪ {q} ∈ K.faces ∧ (e.val ∪ {q}).card = 3)
    rw [Finset.union_singleton]
  | some f =>
    constructor
    · rintro ⟨hne, t, ht, hcard, het, hft⟩
      have hef : e.val ≠ f.val := fun h => hne (Subtype.ext h)
      have hu := Finset.union_eq_triangle (AffineMap.StraddlesZero.card A e.property.2)
        (AffineMap.StraddlesZero.card A f.property.2) hcard het hft hef
      change e.val ∪ f.val ∈ K.faces ∧ (e.val ∪ f.val).card = 3
      rw [hu]
      exact ⟨ht, hcard⟩
    · rintro ⟨ht, hcard⟩
      have hne : e ≠ f := by
        intro h
        subst f
        change (e.val ∪ e.val).card = 3 at hcard
        rw [Finset.union_self, AffineMap.StraddlesZero.card A e.property.2] at hcard
        omega
      exact ⟨hne, e.val ∪ f.val, ht, hcard, Finset.subset_union_left, Finset.subset_union_right⟩

theorem existsUnique_exceptional_neighbor_of_coface (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 → v = q)
    (e : K.strictCrossingEdges A) {t : Finset E}
    (ht : t ∈ K.faces) (hcard : t.card = 3) (het : e.val ⊆ t) :
    ∃! v : Option (K.strictCrossingEdges A),
      e.val ∪ K.exceptionalOriginalVertices A q v = t := by
  classical
  have hne : q ∉ e.val := fun hq => e.property.2.ne_zero hq hAq
  by_cases hqt : q ∈ t
  · have hesub : e.val ⊆ t.erase q := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hne (h ▸ hx), het hx⟩
    have heq : e.val = t.erase q := Finset.eq_of_subset_of_card_le hesub (by
      rw [Finset.card_erase_of_mem hqt, hcard, AffineMap.StraddlesZero.card A e.property.2])
    refine ⟨none, ?_, fun v hv => ?_⟩
    · change e.val ∪ {q} = t
      rw [Finset.union_singleton, heq, Finset.insert_erase hqt]
    · cases v with
      | none => rfl
      | some f =>
        have hqef : q ∈ e.val ∪ f.val := hv.symm ▸ hqt
        rcases Finset.mem_union.mp hqef with he | hf
        · exact False.elim (hne he)
        · exact False.elim (f.property.2.ne_zero hf hAq)
  · have hreg : ∀ v ∈ t, A v ≠ 0 := by
      intro v hv hz
      have hvK := K.down_closed ht (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
      exact hqt (hzero v hvK hz ▸ hv)
    have hecolor := (A.straddlesZero_iff_bichromatic e.val
      (fun v hv => hreg v (het hv))).mp e.property.2
    obtain ⟨f, hf, hfuniq⟩ := hecolor.existsUnique_other hcard het
    have hfA := (A.straddlesZero_iff_bichromatic f (fun v hv => hreg v (hf.2.1 hv))).mpr hf.1
    have hfK : f ∈ K.faces := K.down_closed ht hf.2.1
      (Finset.card_pos.mp (by rw [hf.1.card]; decide))
    let f' : K.strictCrossingEdges A := ⟨f, hfK, hfA⟩
    refine ⟨some f', ?_, fun v hv => ?_⟩
    · exact Finset.union_eq_triangle hecolor.card hf.1.card hcard het hf.2.1 hf.2.2.symm
    · cases v with
      | none =>
        have hqef : q ∈ e.val ∪ {q} := Finset.mem_union_right _ (Finset.mem_singleton_self q)
        exact False.elim (hqt (hv ▸ hqef))
      | some g =>
        have hgt : g.val ⊆ t := hv ▸ Finset.subset_union_right
        have hge : g.val ≠ e.val := by
          intro h
          have hsize : (e.val ∪ g.val).card = 3 := hv ▸ hcard
          rw [h, Finset.union_self, hecolor.card] at hsize
          omega
        have hgcolor := (A.straddlesZero_iff_bichromatic g.val
          (fun w hw => hreg w (hgt hw))).mp g.property.2
        exact congrArg some (Subtype.ext (hfuniq g.val ⟨hgcolor, hgt, hge⟩))

end Geometry.SimplicialComplex
