import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalSliceSegments










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]





theorem exceptionalSliceGraph_carrier (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hq : q ∈ K.vertices) (hAq : A q = 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 → v = q)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    K.space ∩ {x | A x = 0} = {q} ∪
      (K.exceptionalSliceGraph A q).segmentCarrier (K.exceptionalCrossingPoint A q) := by
  ext x
  constructor
  · rintro ⟨hx, hAx⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, hcard, hst⟩ := hpure s hs
    have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono hst hxs
    have hvK (v : E) (hv : v ∈ t) : v ∈ K.vertices :=
      K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hregt (v : E) (hv : v ∈ t) (hvq : v ≠ q) : A v ≠ 0 :=
      fun hz => hvq (hzero v (hvK v hv) hz)
    by_cases hqt : q ∈ t
    · rcases A.exceptional_triangle_slice_eq_singleton_or_segment hcard hqt hAq hregt with
        hsingle | ⟨he, hslice⟩
      · exact Or.inl (hsingle ▸ And.intro hxt hAx)
      · have heK : t.erase q ∈ K.faces := K.down_closed ht (Finset.erase_subset _ _)
          (Finset.card_pos.mp (by rw [AffineMap.StraddlesZero.card A he]; decide))
        let e : K.strictCrossingEdges A := ⟨t.erase q, heK, he⟩
        have hadj : (K.exceptionalSliceGraph A q).Adj none (some e) := by
          change insert q (t.erase q) ∈ K.faces ∧ (insert q (t.erase q)).card = 3
          rw [Finset.insert_erase hqt]
          exact ⟨ht, hcard⟩
        refine Or.inr ⟨none, some e, hadj, ?_⟩
        change x ∈ segment ℝ q (A.straddlingPoint (t.erase q) he)
        rw [← hslice]
        exact ⟨hxt, hAx⟩
    · have hreg : ∀ v ∈ t, A v ≠ 0 :=
        fun v hv => hregt v hv (fun heq => hqt (heq ▸ hv))
      obtain ⟨e, f, he, hf, het, hft, hef, hslice⟩ :=
        A.exists_straddling_edges_triangle hcard hreg ⟨x, hxt, hAx⟩
      have heK : e ∈ K.faces := K.down_closed ht het
        (Finset.card_pos.mp (by rw [AffineMap.StraddlesZero.card A he]; decide))
      have hfK : f ∈ K.faces := K.down_closed ht hft
        (Finset.card_pos.mp (by rw [AffineMap.StraddlesZero.card A hf]; decide))
      let e' : K.strictCrossingEdges A := ⟨e, heK, he⟩
      let f' : K.strictCrossingEdges A := ⟨f, hfK, hf⟩
      have hadj : (K.exceptionalSliceGraph A q).Adj (some e') (some f') :=
        ⟨fun h => hef (congrArg Subtype.val h), t, ht, hcard, het, hft⟩
      refine Or.inr ⟨some e', some f', hadj, ?_⟩
      change x ∈ segment ℝ (A.straddlingPoint e he) (A.straddlingPoint f hf)
      rw [← hslice]
      exact ⟨hxt, hAx⟩
  · rintro (hx | ⟨a, b, hab, hx⟩)
    · rcases mem_singleton_iff.mp hx with rfl
      exact ⟨K.vertices_subset_space hq, hAq⟩
    · obtain ⟨t, ht, _, hslice⟩ := K.exceptionalSliceGraph_segment A hAq hab
      rw [hslice] at hx
      exact ⟨K.convexHull_subset_space ht hx.1, hx.2⟩

end Geometry.SimplicialComplex
