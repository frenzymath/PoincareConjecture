import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Translations.Families



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.UpperTranslation
local notation "P2" => (ℝ × ℝ)

theorem exists_small_translation_whole_family_charts
    {I J : Type*} [Finite I] [Finite J]
    (a b : I → P2) (c d : J → P2) (hcd : ∀ j, c j ≠ d j)
    (hselfA : ∀ i k, i ≠ k →
      segment ℝ (a i) (b i) ∩ segment ℝ (a k) (b k) ⊆ {a i, b i})
    (hselfB : ∀ j k, j ≠ k →
      segment ℝ (c j) (d j) ∩ segment ℝ (c k) (d k) ⊆ {c j, d j})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : P2, ‖v‖ < ε ∧
      ((⋃ i, segment ℝ (a i) (b i)) ∩ ⋃ j, segment ℝ (c j + v) (d j + v)).Finite ∧
      ∀ p ∈ (⋃ i, segment ℝ (a i) (b i)) ∩ ⋃ j, segment ℝ (c j + v) (d j + v),
        ∀ O : Set P2, IsOpen O → p ∈ O →
        ∃ (F : P2 ≃ᴬ[ℝ] P2) (U : Set P2),
          IsOpen U ∧ p ∈ U ∧ U ⊆ O ∧ F 0 = p ∧
          (∀ z, F z ∈ U → (F z ∈ ⋃ i, segment ℝ (a i) (b i) ↔ z.2 = 0)) ∧
          ∀ z, F z ∈ U → (F z ∈ ⋃ j, segment ℝ (c j + v) (d j + v) ↔ z.1 = 0) := by
  obtain ⟨v, hv, hav⟩ := exists_small_translation_avoiding_endpoint_lines a b c d hε
  refine ⟨v, hv, finite_intersection_of_segment_families a b (fun j => c j + v)
    (fun j => d j + v) (fun i j =>
      subsingleton_segment_intersection_of_endpoint_avoiding_line (hav i j).1), ?_⟩
  intro p hp O hO hpO
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp.2
  obtain ⟨ha, hb, hc, hd⟩ := hav i j
  have hopen := open_crossing_of_endpoint_line_avoidance ha hb hc hd ⟨hi, hj⟩
  have hlin := linearIndependent_directions_of_crossing
    (fun h => hcd j (add_right_cancel h)) ha (segment_subset_line _ _ hi) (segment_subset_line _ _ hj)
  have hleft : ∀ k, p ∈ segment ℝ (a k) (b k) → k = i := by
    intro k hk
    by_contra hki
    have hend := hselfA i k (Ne.symm hki) ⟨hi, hk⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hend
    rcases hend with rfl | rfl
    · exact ha (segment_subset_line _ _ hj)
    · exact hb (segment_subset_line _ _ hj)
  have htranslate (k : J) :
      p ∈ segment ℝ (c k + v) (d k + v) ↔ p - v ∈ segment ℝ (c k) (d k) := by
    have hpv : v + (p - v) = p := by abel
    simpa only [hpv, add_comm v (c k), add_comm v (d k)] using
      (mem_segment_translate ℝ v (x := p - v) (b := c k) (c := d k))
  have hright : ∀ k, p ∈ segment ℝ (c k + v) (d k + v) → k = j := by
    intro k hk
    by_contra hkj
    have hend := hselfB j k (Ne.symm hkj) ⟨(htranslate j).mp hj, (htranslate k).mp hk⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hend
    rcases hend with hpc | hpd
    · exact hc ((sub_eq_iff_eq_add.mp hpc) ▸ segment_subset_line _ _ hi)
    · exact hd ((sub_eq_iff_eq_add.mp hpd) ▸ segment_subset_line _ _ hi)
  exact exists_whole_segment_family_crossing a b (fun j => c j + v) (fun j => d j + v)
    i j hlin hopen hleft hright hO hpO

end PoincareConjecture.M76.UpperTranslation
