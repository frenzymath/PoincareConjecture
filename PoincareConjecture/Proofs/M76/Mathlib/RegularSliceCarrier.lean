import PoincareConjecture.Proofs.M76.Mathlib.RegularSliceGraph










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]




theorem regularSliceGraph_carrier (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    K.space ∩ {x | A x = 0} =
      {x | ∃ e f : K.regularCrossingEdges A, (K.regularSliceGraph A).Adj e f ∧
        x ∈ segment ℝ (K.regularCrossingPoint A hreg e) (K.regularCrossingPoint A hreg f)} := by
  ext x
  constructor
  · rintro ⟨hx, hAx⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, hcard, hst⟩ := hpure s hs
    have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono hst hxs
    have hregt : ∀ v ∈ t, A v ≠ 0 := fun v hv => hreg v
      (K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
    obtain ⟨e, f, he, hf, het, hft, hne, hslice⟩ :=
      A.exists_straddling_edges_triangle hcard hregt ⟨x, hxt, hAx⟩
    have heK : e ∈ K.faces := K.down_closed ht het
      (Finset.card_pos.mp (by rw [AffineMap.StraddlesZero.card A he]; decide))
    have hfK : f ∈ K.faces := K.down_closed ht hft
      (Finset.card_pos.mp (by rw [AffineMap.StraddlesZero.card A hf]; decide))
    let e' : K.regularCrossingEdges A := ⟨e, heK,
      (A.straddlesZero_iff_bichromatic e (fun v hv => hregt v (het hv))).mp he⟩
    let f' : K.regularCrossingEdges A := ⟨f, hfK,
      (A.straddlesZero_iff_bichromatic f (fun v hv => hregt v (hft hv))).mp hf⟩
    refine ⟨e', f', ⟨fun h => hne (congrArg Subtype.val h), t, ht, hcard, het, hft⟩, ?_⟩
    change x ∈ segment ℝ (A.straddlingPoint e he) (A.straddlingPoint f hf)
    rw [← hslice]
    exact ⟨hxt, hAx⟩
  · rintro ⟨e, f, hef, hxe⟩
    obtain ⟨t, ht, _, _, _, hslice⟩ := K.regularSliceGraph_segment A hreg hef
    rw [hslice] at hxe
    exact ⟨convexHull_subset_space ht hxe.1, hxe.2⟩

end Geometry.SimplicialComplex
