import PoincareConjecture.Proofs.M76.Mathlib.DerivedStarFaces
import PoincareConjecture.Proofs.M76.Mathlib.TriangleFaceFlags









set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)





theorem derivedSubdivision_pure_triangles
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    ∀ s ∈ (K.derivedSubdivision c hc).faces,
      ∃ t ∈ (K.derivedSubdivision c hc).faces, t.card = 3 ∧ s ⊆ t := by
  classical
  intro s hs
  obtain ⟨a, ha, hchain, rfl⟩ := (K.derivedSubdivision_faces c hc s).mp hs
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
  have him (i : K.faces) (hi : i ∈ a) : i.val ⊆ m.val := by
    rcases hchain i hi m hm with h | h
    · exact h
    · exact hmax hi h
  obtain ⟨t, ht, htc, hmt⟩ := hpure m.val m.property
  have hvalues : ∀ u ∈ a.image Subtype.val, u.Nonempty ∧ u ⊆ t := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨K.nonempty_of_mem_faces i.property, (him i hi).trans hmt⟩
  obtain ⟨p, e, het, hec, hpe, hcover⟩ :=
    Finset.exists_triangle_flag (ha.image Subtype.val) (by
      intro u hu v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      exact hchain i hi j hj) htc hvalues
  have he : e ∈ K.faces := K.down_closed ht het (Finset.card_pos.mp (by omega))
  have hp : {p} ∈ K.faces := K.down_closed he
    (Finset.singleton_subset_iff.mpr hpe) (Finset.singleton_nonempty p)
  let p₀ : K.faces := ⟨{p}, hp⟩
  let e₀ : K.faces := ⟨e, he⟩
  let t₀ : K.faces := ⟨t, ht⟩
  let b : Finset K.faces := {p₀, e₀, t₀}
  have hpe₀ : p₀ ≤ e₀ := Finset.singleton_subset_iff.mpr hpe
  have het₀ : e₀ ≤ t₀ := het
  have hpt₀ : p₀ ≤ t₀ := hpe₀.trans het₀
  have hpe_ne : p₀ ≠ e₀ := by
    intro h
    have hh := congrArg (fun i : K.faces => i.val.card) h
    change ({p} : Finset E).card = e.card at hh
    simp only [Finset.card_singleton, hec] at hh
    omega
  have hpt_ne : p₀ ≠ t₀ := by
    intro h
    have hh := congrArg (fun i : K.faces => i.val.card) h
    change ({p} : Finset E).card = t.card at hh
    simp only [Finset.card_singleton, htc] at hh
    omega
  have het_ne : e₀ ≠ t₀ := by
    intro h
    have hh := congrArg (fun i : K.faces => i.val.card) h
    change e.card = t.card at hh
    omega
  have hbc : b.card = 3 := by simp [b, hpe_ne, hpt_ne, het_ne]
  have hbf : b.image c ∈ (K.derivedSubdivision c hc).faces := by
    apply (K.derivedSubdivision_faces c hc _).mpr
    refine ⟨b, Finset.insert_nonempty _ _, ?_, rfl⟩
    intro i hi j hj
    simp only [b, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl hpe₀
    · exact Or.inl hpt₀
    · exact Or.inr hpe₀
    · exact Or.inl le_rfl
    · exact Or.inl het₀
    · exact Or.inr hpt₀
    · exact Or.inr het₀
    · exact Or.inl le_rfl
  refine ⟨b.image c, hbf, ?_, Finset.image_subset_image ?_⟩
  · exact (Finset.card_image_of_injective b (K.positiveFaceCenter_injective c hc)).trans hbc
  · intro i hi
    rcases hcover i.val (Finset.mem_image.mpr ⟨i, hi, rfl⟩) with h | h | h
    · have hi₀ : i = p₀ := Subtype.ext h
      simp [b, hi₀]
    · have hi₀ : i = e₀ := Subtype.ext h
      simp [b, hi₀]
    · have hi₀ : i = t₀ := Subtype.ext h
      simp [b, hi₀]

end Geometry.SimplicialComplex
