import PoincareConjecture.Proofs.M76.Mathlib.RegularSliceCarrier










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

private theorem crossing_label_choices (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    {e f g : K.regularCrossingEdges A} {t : Finset E} (ht : t.card = 3)
    (het : e.val ⊆ t) (hft : f.val ⊆ t) (hgt : g.val ⊆ t) (hne : e ≠ f) :
    g = e ∨ g = f :=
  ((e.property.2).eq_or_eq_of_subset_triangle f.property.2 g.property.2 ht het hft hgt
    (fun h => hne (Subtype.ext h))).imp Subtype.ext Subtype.ext




theorem regularSliceGraph_segment_inter (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) {e f g k : K.regularCrossingEdges A}
    (hef : (K.regularSliceGraph A).Adj e f) (hgk : (K.regularSliceGraph A).Adj g k) :
    segment ℝ (K.regularCrossingPoint A hreg e) (K.regularCrossingPoint A hreg f) ∩
      segment ℝ (K.regularCrossingPoint A hreg g) (K.regularCrossingPoint A hreg k) ⊆
        convexHull ℝ (({K.regularCrossingPoint A hreg e,
          K.regularCrossingPoint A hreg f} : Set E) ∩
          {K.regularCrossingPoint A hreg g, K.regularCrossingPoint A hreg k}) := by
  obtain ⟨t, ht, htcard, het, hft, htslice⟩ := K.regularSliceGraph_segment A hreg hef
  obtain ⟨u, hu, hucard, hgu, hku, huslice⟩ := K.regularSliceGraph_segment A hreg hgk
  intro x hx
  by_cases htu : t = u
  · subst u
    rcases crossing_label_choices K A htcard het hft hgu hef.1 with rfl | rfl <;>
      rcases crossing_label_choices K A htcard het hft hku hef.1 with rfl | rfl
    · exact (hgk.1 rfl).elim
    · simpa only [inter_self, convexHull_pair] using hx.1
    · simpa only [Set.pair_comm, inter_self, convexHull_pair] using hx.1
    · exact (hgk.1 rfl).elim
  · have hxt := hx.1
    have hxu := hx.2
    rw [htslice] at hxt
    rw [huslice] at hxu
    obtain ⟨q, hq, hqK, hqt, hqu, hpoint⟩ :=
      K.common_straddling_edge_of_triangle_intersection A hreg ht hu htcard hucard htu
        hxt.1 hxu.1 hxt.2
    have hqreg : ∀ v ∈ q, A v ≠ 0 := fun v hv => hreg v
      (K.down_closed hqK (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
    let q' : K.regularCrossingEdges A := ⟨q, hqK,
      (A.straddlesZero_iff_bichromatic q hqreg).mp hq⟩
    have hxq : x = K.regularCrossingPoint A hreg q' := hpoint.symm
    rw [hxq]
    apply subset_convexHull ℝ _
    constructor
    · rcases crossing_label_choices K A htcard het hft (g := q') hqt hef.1 with rfl | rfl
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_singleton _)
    · rcases crossing_label_choices K A hucard hgu hku (g := q') hqu hgk.1 with rfl | rfl
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_singleton _)

end Geometry.SimplicialComplex
