import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic

/-!
# Segment subdivision and finite localization

Elementary ingredients for the local polygon geometry in Cairns (1951),
Theorem 2.1 and Lemma 2.1, pp. 860-861. Segment subdivision retains the
endpoints and degenerate case. Finite closed families can be localized
to any selection containing all members through the chosen point.
See `smale/derivations/2026-09-21-polygon-local-sides.md` for the derivation.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

/-- Splitting a segment at any point gives two segments meeting exactly there;
auxiliary to Cairns, Theorem 2.1 and Lemma 2.1, pp. 860-861. -/
theorem segment_split_at_point {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b q : E} (hq : q ∈ segment ℝ a b) :
    segment ℝ q a ∪ segment ℝ q b = segment ℝ a b ∧
      segment ℝ q a ∩ segment ℝ q b = {q} := by
  by_cases hab : a = b
  · subst b
    have hqa : q = a := by simpa only [segment_same, mem_singleton_iff] using hq
    subst q
    simp
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a b
  have hleft : segment ℝ (L t) a = L '' Icc 0 t := by
    rw [← segment_eq_Icc ht.1, image_segment]
    simpa only [L, AffineMap.lineMap_apply_zero] using segment_symm ℝ (L t) a
  have hright : segment ℝ (L t) b = L '' Icc t 1 := by
    rw [← segment_eq_Icc ht.2, image_segment]
    simp only [L, AffineMap.lineMap_apply_one]
  change segment ℝ (L t) a ∪ segment ℝ (L t) b = segment ℝ a b ∧
    segment ℝ (L t) a ∩ segment ℝ (L t) b = {L t}
  rw [hleft, hright]
  constructor
  · rw [← image_union, Icc_union_Icc_eq_Icc ht.1 ht.2]
    exact (segment_eq_image_lineMap ℝ a b).symm
  · rw [← image_inter (AffineMap.lineMap_injective ℝ hab),
      Icc_inter_Icc_eq_singleton ht.1 ht.2, image_singleton]

/-- A finite closed union locally reduces to the selected sets through a point;
elementary localization for Cairns, Theorem 2.1 and Lemma 2.1, pp. 860-861. -/
theorem exists_open_iUnion_eq_of_mem_imp {X I : Type*} [TopologicalSpace X] [Finite I]
    (S : I → Set X) (hS : ∀ i, IsClosed (S i)) (J : Set I) (q : X)
    (hq : ∀ i, q ∈ S i → i ∈ J) :
    ∃ U : Set X, IsOpen U ∧ q ∈ U ∧
      ∀ z ∈ U, z ∈ ⋃ i, S i ↔ ∃ i ∈ J, z ∈ S i := by
  classical
  refine ⟨(⋃ i ∈ Jᶜ, S i)ᶜ,
    ((Set.toFinite Jᶜ).isClosed_biUnion (fun i _ => hS i)).isOpen_compl, ?_, ?_⟩
  · intro hbad
    obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.mp hbad
    exact hi (hq i hqi)
  · intro z hz
    constructor
    · intro hzu
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hzu
      refine ⟨i, ?_, hzi⟩
      by_contra hi
      exact hz (mem_iUnion₂.mpr ⟨i, hi, hzi⟩)
    · rintro ⟨i, _, hzi⟩
      exact mem_iUnion.mpr ⟨i, hzi⟩

end Poincare.Manifold.Schoenflies.Plane
