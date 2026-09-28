import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Graph

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem existsUnique_triangleSlice_neighbor_of_coface (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (e : K.triangleCrossingEdges A) {t : Finset E}
    (ht : t ∈ K.faces) (htc : t.card = 3) (het : e.val ⊆ t) :
    ∃! v : K.TriangleSliceLabel A,
      e.val ∪ K.triangleSliceOriginalVertices A v = t := by
  classical
  have he := K.triangleCrossingEdge_straddles hA e ht htc het
  by_cases hz : ∃ q ∈ t, A t q = 0
  · obtain ⟨q, hqt, hqzero⟩ := hz
    have hqK : q ∈ K.vertices := K.down_closed ht
      (Finset.singleton_subset_iff.mpr hqt) (Finset.singleton_nonempty q)
    let q' : K.triangleZeroVertices A := ⟨q, hqK, t, ht, htc, hqt, hqzero⟩
    have hqe : q ∉ e.val := fun h => he.ne_zero h hqzero
    have hesub : e.val ⊆ t.erase q := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hqe (h ▸ hx), het hx⟩
    have heq : e.val = t.erase q := Finset.eq_of_subset_of_card_le hesub (by
      rw [Finset.card_erase_of_mem hqt, htc, K.triangleCrossingEdge_card A e])
    refine ⟨.inl q', ?_, ?_⟩
    · change e.val ∪ {q} = t
      rw [Finset.union_singleton, heq, Finset.insert_erase hqt]
    · intro v hv
      cases v with
      | inl r =>
        have hqr : q ∈ e.val ∪ {r.val} := hv.symm ▸ hqt
        have heqr : q = r.val := by
          exact Finset.mem_singleton.mp ((Finset.mem_union.mp hqr).resolve_left hqe)
        exact congrArg Sum.inl (Subtype.ext heqr.symm)
      | inr f =>
        have hft : f.val ⊆ t := hv ▸ Finset.subset_union_right
        have hf := K.triangleCrossingEdge_straddles hA f ht htc hft
        have hqef : q ∈ e.val ∪ f.val := hv.symm ▸ hqt
        exact False.elim (hf.ne_zero ((Finset.mem_union.mp hqef).resolve_left hqe) hqzero)
  · have hreg : ∀ v ∈ t, A t v ≠ 0 := fun v hv hzero => hz ⟨v, hv, hzero⟩
    have hecolor := ((A t).straddlesZero_iff_bichromatic e.val
      (fun v hv => hreg v (het hv))).mp he
    obtain ⟨f, hf, hfuniq⟩ := hecolor.existsUnique_other htc het
    have hfA := ((A t).straddlesZero_iff_bichromatic f
      (fun v hv => hreg v (hf.2.1 hv))).mpr hf.1
    have hfK : f ∈ K.faces := K.down_closed ht hf.2.1
      (Finset.card_pos.mp (by rw [hf.1.card]; decide))
    let f' : K.triangleCrossingEdges A := ⟨f, hfK, t, ht, htc, hf.2.1, hfA⟩
    refine ⟨.inr f', ?_, ?_⟩
    · exact Finset.union_eq_triangle hecolor.card hf.1.card htc het hf.2.1 hf.2.2.symm
    · intro v hv
      cases v with
      | inl q =>
        have hqt : q.val ∈ t := hv ▸ Finset.mem_union_right _ (Finset.mem_singleton_self _)
        exact False.elim (hreg q.val hqt (K.triangleZeroVertex_zero hA q ht htc hqt))
      | inr g =>
        have hgt : g.val ⊆ t := hv ▸ Finset.subset_union_right
        have hge : g.val ≠ e.val := by
          intro h
          have hsize : (e.val ∪ g.val).card = 3 := hv ▸ htc
          rw [h, Finset.union_self, hecolor.card] at hsize
          omega
        have hg := K.triangleCrossingEdge_straddles hA g ht htc hgt
        have hgcolor := ((A t).straddlesZero_iff_bichromatic g.val
          (fun w hw => hreg w (hgt hw))).mp hg
        exact congrArg Sum.inr (Subtype.ext (hfuniq g.val ⟨hgcolor, hgt, hge⟩))

end Geometry.SimplicialComplex
