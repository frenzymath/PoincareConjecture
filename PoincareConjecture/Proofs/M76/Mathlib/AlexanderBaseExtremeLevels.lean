import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.TrivialSectionPositiveSlab

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem mem_vertices_of_face_member (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {v : E} (hv : v ∈ s) : v ∈ K.vertices :=
  K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

theorem extreme_vertex_zero_section (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β) (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v) :
    (∀ x ∈ K.space, 0 ≤ A x) ∧ K.space ∩ {x | A x = 0} = {q} := by
  have hverts (v : E) (hv : v ∈ K.vertices) : 0 ≤ A v := by
    by_cases hvq : v = q
    · rw [hvq, hAq]
    · exact (hβ.trans (hgap v hv hvq)).le
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact convexHull_min (fun v hv => hverts v (mem_vertices_of_face_member K hs hv))
      ((convex_Ici (0 : ℝ)).affine_preimage A) hxs
  · apply Subset.antisymm
    · rintro x ⟨hx, hAx⟩
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      have hz := s.mem_convexHull_zero_vertices A
        (fun v hv => hverts v (mem_vertices_of_face_member K hs hv)) hxs hAx
      have hsub : (s : Set E) ∩ {v | A v = 0} ⊆ {q} := by
        rintro v ⟨hv, hAv⟩
        change A v = 0 at hAv
        by_contra hvq
        have hvq' : v ≠ q := fun h => hvq h
        have hh := hgap v (mem_vertices_of_face_member K hs hv) hvq'
        linarith
      simpa only [convexHull_singleton] using convexHull_mono hsub hz
    · rintro x rfl
      exact ⟨vertices_subset_space hqK, hAq⟩

theorem extreme_vertex_level_homothety (K : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β c : ℝ} (hβ : 0 < β) (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v)
    (hc : c ∈ Ioc 0 β) :
    K.space ∩ {x | A x = c} = AffineMap.homothety q (c / β) ''
      (K.space ∩ {x | A x = β}) := by
  have hzero := (K.extreme_vertex_zero_section A hqK hAq hβ hgap).2
  have htriangle (s : Finset E) (hs : s ∈ K.faces) (hcard : s.card = 3) :
      convexHull ℝ (s : Set E) ∩ {x | A x = c} =
        AffineMap.homothety q (c / β) ''
          (convexHull ℝ (s : Set E) ∩ {x | A x = β}) := by
    apply K.trivial_section_triangle_level_homothety A hqK hAq hβ
      (fun v hv hvq => Or.inr (hgap v hv hvq)) hs hcard _ hc
    rintro x ⟨hx, hAx⟩
    exact hzero.subset ⟨K.convexHull_subset_space hs hx, hAx⟩
  ext x
  constructor
  · rintro ⟨hx, hAx⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, htc, hst⟩ := hpure s hs
    have hxt : x ∈ convexHull ℝ (t : Set E) ∩ {x | A x = c} :=
      ⟨convexHull_mono hst hxs, hAx⟩
    rw [htriangle t ht htc] at hxt
    obtain ⟨y, hy, hxy⟩ := hxt
    exact ⟨y, ⟨K.convexHull_subset_space ht hy.1, hy.2⟩, hxy⟩
  · rintro ⟨y, ⟨hy, hAy⟩, rfl⟩
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy
    obtain ⟨t, ht, htc, hst⟩ := hpure s hs
    have hyt : y ∈ convexHull ℝ (t : Set E) ∩ {x | A x = β} :=
      ⟨convexHull_mono hst hys, hAy⟩
    have hx := (htriangle t ht htc).symm.subset
      (mem_image_of_mem (AffineMap.homothety q (c / β)) hyt)
    exact ⟨K.convexHull_subset_space ht hx.1, hx.2⟩

theorem extreme_vertex_top_section_nonempty (K : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β) (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v) :
    (K.space ∩ {x | A x = β}).Nonempty := by
  classical
  obtain ⟨s, hs, hsc, hqs⟩ := hpure {q} hqK
  have hq : q ∈ s := hqs (Finset.mem_singleton_self q)
  obtain ⟨v, hvs, hvq⟩ : ∃ v ∈ s, v ≠ q := by
    by_contra! h
    have hsub : s ⊆ {q} := fun v hv => Finset.mem_singleton.mpr (h v hv)
    have hcard := Finset.card_le_card hsub
    simp only [hsc, Finset.card_singleton] at hcard
    omega
  have hβv := hgap v (mem_vertices_of_face_member K hs hvs) hvq
  have hvpos : 0 < A v := hβ.trans hβv
  have hr : β / A v ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hβ.le hvpos.le, (div_le_one hvpos).mpr hβv.le⟩
  refine ⟨AffineMap.lineMap q v (β / A v), ?_, ?_⟩
  · apply K.convexHull_subset_space hs
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ hq) (subset_convexHull ℝ _ hvs)
      (lineMap_mem_segment ℝ q v hr)
  · change A (AffineMap.lineMap q v (β / A v)) = β
    rw [A.apply_lineMap, hAq, AffineMap.lineMap_apply_ring', sub_zero, add_zero,
      div_mul_cancel₀ β hvpos.ne']

theorem extreme_vertex_sublevel_eq_convexJoin (K : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β) (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v) :
    K.space ∩ {x | A x ≤ β} = convexJoin ℝ {q} (K.space ∩ {x | A x = β}) := by
  obtain ⟨hnonneg, hzero⟩ := K.extreme_vertex_zero_section A hqK hAq hβ hgap
  have htop := K.extreme_vertex_top_section_nonempty hpure A hqK hAq hβ hgap
  ext x
  constructor
  · rintro ⟨hx, hxβ⟩
    by_cases hx0 : A x = 0
    · have hxq : x = q := hzero.subset ⟨hx, hx0⟩
      subst x
      obtain ⟨y, hy⟩ := htop
      exact mem_convexJoin.mpr ⟨q, mem_singleton q, y, hy, left_mem_segment ℝ q y⟩
    · have hc : A x ∈ Ioc 0 β := ⟨lt_of_le_of_ne (hnonneg x hx) (Ne.symm hx0), hxβ⟩
      have hxlevel : x ∈ K.space ∩ {y | A y = A x} := ⟨hx, rfl⟩
      rw [K.extreme_vertex_level_homothety hpure A hqK hAq hβ hgap hc] at hxlevel
      obtain ⟨y, hy, hxy⟩ := hxlevel
      refine mem_convexJoin.mpr ⟨q, mem_singleton q, y, hy, ?_⟩
      rw [← hxy, AffineMap.homothety_eq_lineMap]
      exact lineMap_mem_segment ℝ q y ⟨div_nonneg hc.1.le hβ.le, (div_le_one hβ).mpr hc.2⟩
  · intro hx
    obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hx
    have haq : a = q := ha
    subst a
    rw [segment_eq_image_lineMap] at hxy
    obtain ⟨r, hr, rfl⟩ := hxy
    by_cases hr0 : r = 0
    · subst r
      rw [AffineMap.lineMap_apply_zero]
      refine ⟨vertices_subset_space hqK, ?_⟩
      change A q ≤ β
      rw [hAq]
      exact hβ.le
    · have hc : r * β ∈ Ioc 0 β := ⟨mul_pos (lt_of_le_of_ne hr.1 (Ne.symm hr0)) hβ,
        by nlinarith [hr.2]⟩
      have hxlevel : AffineMap.lineMap q y r ∈ K.space ∩ {x | A x = r * β} := by
        rw [K.extreme_vertex_level_homothety hpure A hqK hAq hβ hgap hc]
        refine ⟨y, hy, ?_⟩
        rw [mul_div_cancel_right₀ r hβ.ne', AffineMap.homothety_eq_lineMap]
      exact ⟨hxlevel.1, hxlevel.2.trans_le hc.2⟩

end Geometry.SimplicialComplex
