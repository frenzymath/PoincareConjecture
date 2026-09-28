import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Translations.Coordinates
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.UpperTranslation
local notation "P2" => (ℝ × ℝ)

theorem finite_intersection_of_segment_families
    {I J : Type*} [Finite I] [Finite J]
    (a b : I → P2) (c d : J → P2)
    (hpair : ∀ i j, (segment ℝ (a i) (b i) ∩ segment ℝ (c j) (d j)).Subsingleton) :
    ((⋃ i, segment ℝ (a i) (b i)) ∩ ⋃ j, segment ℝ (c j) (d j)).Finite := by
  apply (Set.finite_iUnion (fun i => Set.finite_iUnion (fun j => (hpair i j).finite))).subset
  rintro p ⟨hpA, hpB⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hpA
  obtain ⟨j, hj⟩ := mem_iUnion.mp hpB
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, hi, hj⟩⟩

theorem exists_whole_segment_family_crossing
    {I J : Type*} [Finite I] [Finite J]
    (a b : I → P2) (c d : J → P2) (i : I) (j : J) {p : P2}
    (h : LinearIndependent ℝ ![b i - a i, d j - c j])
    (hp : p ∈ openSegment ℝ (a i) (b i) ∩ openSegment ℝ (c j) (d j))
    (hleft : ∀ k, p ∈ segment ℝ (a k) (b k) → k = i)
    (hright : ∀ k, p ∈ segment ℝ (c k) (d k) → k = j)
    {O : Set P2} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (F : P2 ≃ᴬ[ℝ] P2) (U : Set P2),
      IsOpen U ∧ p ∈ U ∧ U ⊆ O ∧ F 0 = p ∧
      (∀ z, F z ∈ U → (F z ∈ ⋃ k, segment ℝ (a k) (b k) ↔ z.2 = 0)) ∧
      ∀ z, F z ∈ U → (F z ∈ ⋃ k, segment ℝ (c k) (d k) ↔ z.1 = 0) := by
  let Left := ⋃ k : {k : I // k ≠ i}, segment ℝ (a k) (b k)
  let Right := ⋃ k : {k : J // k ≠ j}, segment ℝ (c k) (d k)
  have hclosed (x y : P2) : IsClosed (segment ℝ x y) := by
    simpa only [convexHull_pair] using
      ((Set.finite_singleton y).insert x |>.isCompact_convexHull ℝ).isClosed
  have hclosedL : IsClosed Left := isClosed_iUnion_of_finite (fun _ => hclosed _ _)
  have hclosedR : IsClosed Right := isClosed_iUnion_of_finite (fun _ => hclosed _ _)
  let W := O ∩ Leftᶜ ∩ Rightᶜ
  have hW : IsOpen W := (hO.inter hclosedL.isOpen_compl).inter hclosedR.isOpen_compl
  have hpW : p ∈ W := by
    refine ⟨⟨hpO, ?_⟩, ?_⟩
    · intro hh
      obtain ⟨k, hk⟩ := mem_iUnion.mp hh
      exact k.property (hleft k hk)
    · intro hh
      obtain ⟨k, hk⟩ := mem_iUnion.mp hh
      exact k.property (hright k hk)
  obtain ⟨F, U, hU, hpU, hUW, hF, hfirst, hsecond⟩ :=
    exists_affine_open_segment_crossing h hp hW hpW
  refine ⟨F, U, hU, hpU, hUW.trans (inter_subset_left.trans inter_subset_left), hF, ?_, ?_⟩
  · intro z hz
    rw [← hfirst z hz]
    constructor
    · intro hh
      obtain ⟨k, hk⟩ := mem_iUnion.mp hh
      by_cases hki : k = i
      · exact hki ▸ hk
      · exact False.elim ((hUW hz).1.2 (mem_iUnion.mpr ⟨⟨k, hki⟩, hk⟩))
    · exact fun hh => mem_iUnion.mpr ⟨i, hh⟩
  · intro z hz
    rw [← hsecond z hz]
    constructor
    · intro hh
      obtain ⟨k, hk⟩ := mem_iUnion.mp hh
      by_cases hkj : k = j
      · exact hkj ▸ hk
      · exact False.elim ((hUW hz).2 (mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩))
    · exact fun hh => mem_iUnion.mpr ⟨j, hh⟩

end PoincareConjecture.M76.UpperTranslation
