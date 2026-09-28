import PoincareConjecture.Proofs.M76.Mathlib.StrictCrossingPointIncidence
import PoincareConjecture.Proofs.M76.Mathlib.ResidualLevelScaling

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem vertex_and_positive_others_of_trivial_section_slab_point
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices)
    {β : ℝ} (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z)
    {s : Finset E} (hs : s ∈ K.faces)
    (hsection : convexHull ℝ (s : Set E) ∩ {z | A z = 0} ⊆ {q})
    {x : E} (hxs : x ∈ convexHull ℝ (s : Set E)) (hxA : A x ∈ Ioc 0 β) :
    q ∈ s ∧ ∀ z ∈ s, z ≠ q → β < A z := by
  classical
  have hpositive : ∃ v ∈ s, 0 < A v := by
    by_contra h
    push Not at h
    have hxnonpos : A x ≤ 0 :=
      convexHull_min h ((convex_Iic (0 : ℝ)).affine_preimage A) hxs
    exact hxA.1.not_ge hxnonpos
  obtain ⟨v, hvs, hv⟩ := hpositive
  have hnotneg (z : E) (hzs : z ∈ s) : ¬A z < 0 := by
    intro hz
    let e : Finset E := {z, v}
    have hes : e ⊆ s := by simp [e, Finset.insert_subset_iff, hzs, hvs]
    have he : e ∈ K.faces := K.down_closed hs hes (by simp [e])
    have hAe : A.StraddlesZero e := ⟨z, v, hz, hv, by simp [e]⟩
    have hp := A.straddlingPoint_mem e hAe
    have hpq : A.straddlingPoint e hAe = q :=
      mem_singleton_iff.mp (hsection ⟨convexHull_mono hes hp.1, hp.2⟩)
    exact K.straddlingPoint_ne_vertex A he hAe hqK hpq
  have hother (z : E) (hz : z ∈ s) (hzq : z ≠ q) : β < A z :=
    (hreg z (K.down_closed hs (Finset.singleton_subset_iff.mpr hz)
      (Finset.singleton_nonempty z)) hzq).resolve_left (hnotneg z hz)
  refine ⟨?_, hother⟩
  by_contra hqs
  have hverts : ∀ z ∈ s, β < A z :=
    fun z hz => hother z hz (fun h => hqs (h ▸ hz))
  have hxabove : β < A x :=
    convexHull_min hverts ((convex_Ioi β).affine_preimage A) hxs
  exact hxabove.not_ge hxA.2

theorem trivial_section_triangle_level_homothety
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) {q : E}
    (hqK : q ∈ K.vertices) (hAq : A q = 0) {β c : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z)
    {s : Finset E} (hs : s ∈ K.faces) (hsc : s.card = 3)
    (hsection : convexHull ℝ (s : Set E) ∩ {z | A z = 0} ⊆ {q})
    (hc : c ∈ Ioc 0 β) :
    convexHull ℝ (s : Set E) ∩ {x | A x = c} =
      AffineMap.homothety q (c / β) ''
        (convexHull ℝ (s : Set E) ∩ {x | A x = β}) := by
  classical
  by_cases hpos : ∃ x ∈ convexHull ℝ (s : Set E), A x ∈ Ioc 0 β
  · obtain ⟨x, hxs, hxA⟩ := hpos
    obtain ⟨hqs, hother⟩ :=
      K.vertex_and_positive_others_of_trivial_section_slab_point A hqK hreg hs hsection hxs hxA
    have hcard : (s.erase q).card = 2 := by rw [Finset.card_erase_of_mem hqs, hsc]
    obtain ⟨u, v, _, huv⟩ := Finset.card_eq_two.mp hcard
    have hu : u ∈ s.erase q := by rw [huv]; simp
    have hv : v ∈ s.erase q := by rw [huv]; simp
    have hset : (s : Set E) = insert q {u, v} := by
      rw [← Finset.insert_erase hqs, huv]
      simp
    rw [hset]
    exact A.positive_triangle_level_homothety hAq hβ
      (hother u (Finset.mem_erase.mp hu).2 (Finset.mem_erase.mp hu).1)
      (hother v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1) hc
  · have hempty (t : ℝ) (ht : t ∈ Ioc 0 β) :
        convexHull ℝ (s : Set E) ∩ {x | A x = t} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hpos
      refine ⟨x, hx.1, ?_⟩
      rw [hx.2]
      exact ht
    rw [hempty c hc, hempty β ⟨hβ, le_rfl⟩, image_empty]

end Geometry.SimplicialComplex
