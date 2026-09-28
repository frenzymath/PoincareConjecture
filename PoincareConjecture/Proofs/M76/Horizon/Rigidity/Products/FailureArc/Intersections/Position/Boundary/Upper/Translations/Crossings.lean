import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Translations.Avoidance

set_option autoImplicit false
open Set AffineSubspace

namespace PoincareConjecture.M76.UpperTranslation
local notation "P2" => (ℝ × ℝ)

theorem segment_subset_line (a b : P2) :
    segment ℝ a b ⊆ (affineSpan ℝ ({a, b} : Set P2) : Set P2) := by
  simpa only [convexHull_pair] using convexHull_subset_affineSpan (𝕜 := ℝ) ({a, b} : Set P2)

theorem subsingleton_segment_intersection_of_endpoint_avoiding_line
    {a b c d : P2} (ha : a ∉ affineSpan ℝ ({c, d} : Set P2)) :
    (segment ℝ a b ∩ segment ℝ c d).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have heq := (affineSpan_pair_eq_of_mem_of_mem_of_ne
    (segment_subset_line a b hx.1) (segment_subset_line a b hy.1) hxy).symm.trans
    (affineSpan_pair_eq_of_mem_of_mem_of_ne
      (segment_subset_line c d hx.2) (segment_subset_line c d hy.2) hxy)
  exact ha (heq ▸ left_mem_affineSpan_pair ℝ a b)

theorem linearIndependent_directions_of_crossing
    {a b c d x : P2} (hcd : c ≠ d)
    (ha : a ∉ affineSpan ℝ ({c, d} : Set P2))
    (hx : x ∈ affineSpan ℝ ({a, b} : Set P2))
    (hx' : x ∈ affineSpan ℝ ({c, d} : Set P2)) :
    LinearIndependent ℝ ![b - a, d - c] := by
  rw [linearIndependent_fin2]
  refine ⟨sub_ne_zero.mpr hcd.symm, ?_⟩
  intro r hr
  change r • (d - c) = b - a at hr
  have hd : d - c ∈ (affineSpan ℝ ({c, d} : Set P2)).direction :=
    vsub_mem_direction (right_mem_affineSpan_pair ℝ c d) (left_mem_affineSpan_pair ℝ c d)
  have hu : b - a ∈ (affineSpan ℝ ({c, d} : Set P2)).direction :=
    hr ▸ (affineSpan ℝ ({c, d} : Set P2)).direction.smul_mem r hd
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  have hm := vadd_mem_of_mem_direction
    ((affineSpan ℝ ({c, d} : Set P2)).direction.neg_mem
      ((affineSpan ℝ ({c, d} : Set P2)).direction.smul_mem t hu)) hx'
  apply ha
  have heq : -(t • (b - a)) + x = a := by
    rw [← ht, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    abel
  simpa only [vadd_eq_add, heq] using hm

theorem open_crossing_of_endpoint_line_avoidance
    {a b c d x : P2}
    (ha : a ∉ affineSpan ℝ ({c, d} : Set P2))
    (hb : b ∉ affineSpan ℝ ({c, d} : Set P2))
    (hc : c ∉ affineSpan ℝ ({a, b} : Set P2))
    (hd : d ∉ affineSpan ℝ ({a, b} : Set P2))
    (hx : x ∈ segment ℝ a b ∩ segment ℝ c d) :
    x ∈ openSegment ℝ a b ∩ openSegment ℝ c d := by
  exact ⟨mem_openSegment_of_ne_left_right
    (fun h => ha (h.symm ▸ segment_subset_line c d hx.2))
    (fun h => hb (h.symm ▸ segment_subset_line c d hx.2)) hx.1,
    mem_openSegment_of_ne_left_right
      (fun h => hc (h.symm ▸ segment_subset_line a b hx.1))
      (fun h => hd (h.symm ▸ segment_subset_line a b hx.1)) hx.2⟩

theorem exists_small_translation_transverse_segments
    {I J : Type*} [Finite I] [Finite J]
    (a b : I → P2) (c d : J → P2) (hcd : ∀ j, c j ≠ d j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : P2, ‖v‖ < ε ∧ ∀ i j,
      (segment ℝ (a i) (b i) ∩ segment ℝ (c j + v) (d j + v)).Subsingleton ∧
      ∀ x ∈ segment ℝ (a i) (b i) ∩ segment ℝ (c j + v) (d j + v),
        x ∈ openSegment ℝ (a i) (b i) ∩ openSegment ℝ (c j + v) (d j + v) ∧
        LinearIndependent ℝ ![b i - a i, d j - c j] := by
  obtain ⟨v, hv, hav⟩ := exists_small_translation_avoiding_endpoint_lines a b c d hε
  refine ⟨v, hv, fun i j => ?_⟩
  obtain ⟨ha, hb, hc, hd⟩ := hav i j
  refine ⟨subsingleton_segment_intersection_of_endpoint_avoiding_line ha, fun x hx => ?_⟩
  refine ⟨open_crossing_of_endpoint_line_avoidance ha hb hc hd hx, ?_⟩
  have hcd' : c j + v ≠ d j + v := fun h => hcd j (add_right_cancel h)
  have hh := linearIndependent_directions_of_crossing hcd' ha
    (segment_subset_line _ _ hx.1) (segment_subset_line _ _ hx.2)
  simpa only [add_sub_add_right_eq_sub] using hh

end PoincareConjecture.M76.UpperTranslation
