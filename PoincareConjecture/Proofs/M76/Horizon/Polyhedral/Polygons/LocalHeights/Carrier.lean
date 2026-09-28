import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Segments

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem triangle_zero_unique_of_no_zero_edges (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ)
    (hnozero : ∀ e ∈ K.faces, e.card = 2 → ∃ q ∈ e, q ∉ K.triangleZeroVertices A)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3)
    {q v : E} (hqt : q ∈ t) (hvt : v ∈ t) (hq : A t q = 0) (hv : A t v = 0) : v = q := by
  by_contra hvq
  have he : ({q, v} : Finset E) ∈ K.faces := K.down_closed ht
    (by simp [Finset.insert_subset_iff, hqt, hvt]) (by simp)
  have hqK : q ∈ K.vertices := K.down_closed ht
    (Finset.singleton_subset_iff.mpr hqt) (Finset.singleton_nonempty q)
  have hvK : v ∈ K.vertices := K.down_closed ht
    (Finset.singleton_subset_iff.mpr hvt) (Finset.singleton_nonempty v)
  obtain ⟨w, hw, hwnot⟩ := hnozero {q, v} he (by simp [Ne.symm hvq])
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact hwnot ⟨hqK, t, ht, htc, hqt, hq⟩
  · exact hwnot ⟨hvK, t, ht, htc, hvt, hv⟩

theorem triangleSliceGraph_carrier (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (hnozero : ∀ e ∈ K.faces, e.card = 2 → ∃ q ∈ e, q ∉ K.triangleZeroVertices A) :
    K.triangleZeroSet A = K.triangleZeroVertices A ∪
      (K.triangleSliceGraph A).segmentCarrier (K.triangleSlicePoint A) := by
  ext x
  constructor
  · rintro ⟨t, ht, htc, hxt, hAx⟩
    have hvK (v : E) (hv : v ∈ t) : v ∈ K.vertices :=
      K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    by_cases hz : ∃ q ∈ t, A t q = 0
    · obtain ⟨q, hqt, hqzero⟩ := hz
      have hreg : ∀ v ∈ t, v ≠ q → A t v ≠ 0 := by
        intro v hvt hvq hvzero
        exact hvq (K.triangle_zero_unique_of_no_zero_edges A hnozero ht htc hqt hvt hqzero hvzero)
      let q' : K.triangleZeroVertices A := ⟨q, hvK q hqt, t, ht, htc, hqt, hqzero⟩
      rcases (A t).exceptional_triangle_slice_eq_singleton_or_segment htc hqt hqzero hreg with
          hsingle | ⟨he, hslice⟩
      · have hxq : x = q := mem_singleton_iff.mp (hsingle ▸ And.intro hxt hAx)
        exact Or.inl (hxq.symm ▸ q'.property)
      · have heK : t.erase q ∈ K.faces := K.down_closed ht (Finset.erase_subset _ _)
          (Finset.card_pos.mp (by rw [he.card]; decide))
        let e : K.triangleCrossingEdges A :=
          ⟨t.erase q, heK, t, ht, htc, Finset.erase_subset _ _, he⟩
        have hadj : (K.triangleSliceGraph A).Adj (.inl q') (.inr e) := by
          change ({q} ∪ t.erase q ∈ K.faces ∧ ({q} ∪ t.erase q).card = 3)
          rw [Finset.singleton_union, Finset.insert_erase hqt]
          exact ⟨ht, htc⟩
        refine Or.inr ⟨.inl q', .inr e, hadj, ?_⟩
        change x ∈ segment ℝ q (K.triangleCrossingPoint A e)
        rw [K.triangleCrossingPoint_eq hA e ht htc (Finset.erase_subset _ _) he, ← hslice]
        exact ⟨hxt, hAx⟩
    · have hreg : ∀ v ∈ t, A t v ≠ 0 := fun v hv hvzero => hz ⟨v, hv, hvzero⟩
      obtain ⟨e, f, he, hf, het, hft, hef, hslice⟩ :=
        (A t).exists_straddling_edges_triangle htc hreg ⟨x, hxt, hAx⟩
      have heK : e ∈ K.faces := K.down_closed ht het
        (Finset.card_pos.mp (by rw [he.card]; decide))
      have hfK : f ∈ K.faces := K.down_closed ht hft
        (Finset.card_pos.mp (by rw [hf.card]; decide))
      let e' : K.triangleCrossingEdges A := ⟨e, heK, t, ht, htc, het, he⟩
      let f' : K.triangleCrossingEdges A := ⟨f, hfK, t, ht, htc, hft, hf⟩
      have hunion := Finset.union_eq_triangle he.card hf.card htc het hft hef
      have hadj : (K.triangleSliceGraph A).Adj (.inr e') (.inr f') := by
        change e ∪ f ∈ K.faces ∧ (e ∪ f).card = 3
        rw [hunion]
        exact ⟨ht, htc⟩
      refine Or.inr ⟨.inr e', .inr f', hadj, ?_⟩
      change x ∈ segment ℝ (K.triangleCrossingPoint A e') (K.triangleCrossingPoint A f')
      rw [K.triangleCrossingPoint_eq hA e' ht htc het he,
        K.triangleCrossingPoint_eq hA f' ht htc hft hf, ← hslice]
      exact ⟨hxt, hAx⟩
  · rintro (hx | ⟨a, b, hab, hx⟩)
    · exact K.triangleSlicePoint_mem A (.inl ⟨x, hx⟩)
    · rw [K.triangleSliceGraph_segment hA hab] at hx
      exact hx.2

end Geometry.SimplicialComplex
