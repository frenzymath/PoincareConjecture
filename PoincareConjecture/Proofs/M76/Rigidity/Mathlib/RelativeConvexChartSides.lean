import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeChartRestriction
import PoincareConjecture.Proofs.M76.Mathlib.LocalRegionSideIncidence
import Mathlib.Analysis.Convex.Topology










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem halfspace_of_convex_subtype_frontier_chart
    {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : IsClosed D) (hreg : closure (interior D) = D)
    {p : X} (hp : p ∈ frontier D) {M : Set C3}
    (r : OpenPartialHomeomorph X M) (hpR : p ∈ r.source)
    (hcv : Convex ℝ ((Subtype.val : M → C3) '' r.target))
    (hfront : ∀ x ∈ r.source, x ∈ frontier D ↔ (r x : C3).2 = 0) :
    (∀ x ∈ r.source, x ∈ D ↔ 0 ≤ (r x : C3).2) ∨
      (∀ x ∈ r.source, x ∈ D ↔ (r x : C3).2 ≤ 0) := by
  let P : Set M := r.target ∩ {y | 0 < (y : C3).2}
  let N : Set M := r.target ∩ {y | (y : C3).2 < 0}
  have hside (S : Set ℝ) (hS : Convex ℝ S) :
      IsPreconnected (r.target ∩ {y : M | (y : C3).2 ∈ S}) := by
    have himage : (Subtype.val : M → C3) ''
        (r.target ∩ {y : M | (y : C3).2 ∈ S}) =
        ((Subtype.val : M → C3) '' r.target) ∩
          (LinearMap.snd ℝ (ℝ × ℝ) ℝ) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz.1, rfl⟩, hz.2⟩
      · rintro ⟨⟨z, hz, rfl⟩, hy⟩
        exact ⟨z, ⟨hz, hy⟩, rfl⟩
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [himage]
    exact (hcv.inter (hS.linear_preimage (LinearMap.snd ℝ (ℝ × ℝ) ℝ))).isPreconnected
  have hP : IsPreconnected (r.symm '' P) :=
    (hside (Ioi 0) (convex_Ioi 0)).image r.symm
      (r.continuousOn_symm.mono inter_subset_left)
  have hN : IsPreconnected (r.symm '' N) :=
    (hside (Iio 0) (convex_Iio 0)).image r.symm
      (r.continuousOn_symm.mono inter_subset_left)
  have hPmem (x : X) (hx : x ∈ r.source) :
      x ∈ r.symm '' P ↔ 0 < (r x : C3).2 := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [r.right_inv hy.1]
      exact hy.2
    · intro ht
      exact ⟨r x, ⟨r.map_source hx, ht⟩, r.left_inv hx⟩
  have hNmem (x : X) (hx : x ∈ r.source) :
      x ∈ r.symm '' N ↔ (r x : C3).2 < 0 := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [r.right_inv hy.1]
      exact hy.2
    · intro ht
      exact ⟨r x, ⟨r.map_source hx, ht⟩, r.left_inv hx⟩
  have hcover : r.source \ frontier D = (r.symm '' P) ∪ (r.symm '' N) := by
    ext x
    constructor
    · rintro ⟨hx, hxf⟩
      have hne : (r x : C3).2 ≠ 0 := fun h => hxf ((hfront x hx).mpr h)
      rcases lt_or_gt_of_ne hne with ht | ht
      · exact Or.inr ((hNmem x hx).mpr ht)
      · exact Or.inl ((hPmem x hx).mpr ht)
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · refine ⟨r.map_target hy.1, ?_⟩
        intro hf
        have heq := (hfront (r.symm y) (r.map_target hy.1)).mp hf
        rw [r.right_inv hy.1] at heq
        exact (ne_of_gt hy.2) heq
      · refine ⟨r.map_target hy.1, ?_⟩
        intro hf
        have heq := (hfront (r.symm y) (r.map_target hy.1)).mp hf
        rw [r.right_inv hy.1] at heq
        exact (ne_of_lt hy.2) heq
  have hzero (x : X) (hx : x ∈ r.source) (ht : (r x : C3).2 = 0) : x ∈ D :=
    hD.frontier_subset ((hfront x hx).mpr ht)
  rcases hD.local_complementary_sides hreg hp r.open_source hpR hP hN hcover with h | h
  · left
    intro x hx
    constructor
    · intro hxD
      by_contra hn
      exact h.2 ((hNmem x hx).mpr (lt_of_not_ge hn)) hxD
    · intro ht
      rcases eq_or_lt_of_le ht with heq | hlt
      · exact hzero x hx heq.symm
      · exact interior_subset (h.1 ((hPmem x hx).mpr hlt))
  · right
    intro x hx
    constructor
    · intro hxD
      by_contra hn
      exact h.2 ((hPmem x hx).mpr (lt_of_not_ge hn)) hxD
    · intro ht
      rcases eq_or_lt_of_le ht with heq | hlt
      · exact hzero x hx heq
      · exact interior_subset (h.1 ((hNmem x hx).mpr hlt))




theorem relative_halfspace_of_convex_frontier_chart
    {X : Type*} [TopologicalSpace X] {R K : Set X} (hKR : K ⊆ R)
    (hK : IsClosed ((Subtype.val : R → X) ⁻¹' K))
    (hreg : closure (interior ((Subtype.val : R → X) ⁻¹' K)) =
      (Subtype.val : R → X) ⁻¹' K)
    {p : R} (hp : p ∈ frontier ((Subtype.val : R → X) ⁻¹' K))
    (H : OpenPartialHomeomorph X C3) (hpH : (p : X) ∈ H.source)
    {M : Set C3} (himage : H.IsImage R M) (hcv : Convex ℝ (H.target ∩ M))
    (hfront : ∀ x : R, (x : X) ∈ H.source →
      (x ∈ frontier ((Subtype.val : R → X) ⁻¹' K) ↔ (H x).2 = 0)) :
    (∀ x ∈ H.source, x ∈ K ↔ x ∈ R ∧ 0 ≤ (H x).2) ∨
      (∀ x ∈ H.source, x ∈ K ↔ x ∈ R ∧ (H x).2 ≤ 0) := by
  obtain ⟨r, hrS, hrT, hrval, _⟩ := himage.exists_subtype_chart p hpH
  have htarget : (Subtype.val : M → C3) '' r.target = H.target ∩ M := by
    rw [hrT]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.property⟩
    · intro hy
      exact ⟨⟨y, hy.2⟩, hy.1, rfl⟩
  have hrcv : Convex ℝ ((Subtype.val : M → C3) '' r.target) := htarget.symm ▸ hcv
  have hrf : ∀ x ∈ r.source,
      x ∈ frontier ((Subtype.val : R → X) ⁻¹' K) ↔ (r x : C3).2 = 0 := by
    intro x hx
    rw [hrval x hx]
    exact hfront x (hrS.subset hx)
  have htransfer (q : ℝ → Prop)
      (hq : ∀ x ∈ r.source, x ∈ (Subtype.val : R → X) ⁻¹' K ↔ q (r x : C3).2) :
      ∀ x ∈ H.source, x ∈ K ↔ x ∈ R ∧ q (H x).2 := by
    intro x hx
    by_cases hxR : x ∈ R
    · have hxs : (⟨x, hxR⟩ : R) ∈ r.source := hrS.symm.subset hx
      have h := hq ⟨x, hxR⟩ hxs
      rw [hrval ⟨x, hxR⟩ hxs] at h
      exact h.trans (and_iff_right hxR).symm
    · constructor
      · intro hxK
        exact False.elim (hxR (hKR hxK))
      · intro h
        exact False.elim (hxR h.1)
  rcases halfspace_of_convex_subtype_frontier_chart hK hreg hp r
      (hrS.symm.subset hpH) hrcv hrf with h | h
  · exact Or.inl (htransfer (fun t => 0 ≤ t) h)
  · exact Or.inr (htransfer (fun t => t ≤ 0) h)

end PoincareConjecture.M76
