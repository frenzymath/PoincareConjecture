import PoincareConjecture.Proofs.M76.Mathlib.PlanarSegmentHeight
import PoincareConjecture.Proofs.M76.Mathlib.ContinuousGraphShear

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PlanarSegment

theorem fst_mem_uIoo_of_mem_segment {a b q : ℝ × ℝ} (hab : a.1 ≠ b.1)
    (hq : q ∈ segment ℝ a b) (hqa : q ≠ a) (hqb : q ≠ b) :
    q.1 ∈ uIoo a.1 b.1 := by
  have hm := (mem_segment_iff hab).mp hq
  have hqa' : q.1 ≠ a.1 := by
    intro heq
    apply hqa
    exact Prod.ext heq (by rw [hm.2, heq, height_left])
  have hqb' : q.1 ≠ b.1 := by
    intro heq
    apply hqb
    exact Prod.ext heq (by rw [hm.2, heq, height_right hab])
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · rw [uIcc_of_le hlt.le] at hm
    exact mem_uIoo_of_lt (lt_of_le_of_ne hm.1.1 hqa'.symm)
      (lt_of_le_of_ne hm.1.2 hqb')
  · rw [uIcc_of_ge hlt.le] at hm
    exact mem_uIoo_of_gt (lt_of_le_of_ne hm.1.1 hqb'.symm)
      (lt_of_le_of_ne hm.1.2 hqa')

theorem exists_local_line_of_nonvertical {a b q : ℝ × ℝ} (hab : a.1 ≠ b.1)
    (hq : q ∈ segment ℝ a b) (hqa : q ≠ a) (hqb : q ≠ b) :
    ∃ e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (e q).2 = 0 ∧
      ∀ᶠ x in 𝓝 q, x ∈ segment ℝ a b ↔ (e x).2 = 0 := by
  let e := Homeomorph.subContinuousGraph (height a b) (continuous_height a b)
  have hzero (x : ℝ × ℝ) : (e x).2 = 0 ↔ x.2 = height a b x.1 :=
    Homeomorph.subContinuousGraph_snd_eq_zero_iff _ _ x
  refine ⟨e, (hzero q).mpr ((mem_segment_iff hab).mp hq).2, ?_⟩
  have hnhds : ∀ᶠ x in 𝓝 q, x.1 ∈ uIoo a.1 b.1 :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds
      (fst_mem_uIoo_of_mem_segment hab hq hqa hqb)
  filter_upwards [hnhds] with x hx
  rw [mem_segment_iff hab, hzero x]
  exact and_iff_right (uIoo_subset_uIcc_self hx)

theorem exists_local_line {a b q : ℝ × ℝ}
    (hq : q ∈ segment ℝ a b) (hqa : q ≠ a) (hqb : q ≠ b) :
    ∃ e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (e q).2 = 0 ∧
      ∀ᶠ x in 𝓝 q, x ∈ segment ℝ a b ↔ (e x).2 = 0 := by
  by_cases hab : a.1 = b.1
  · have hab' : a.2 ≠ b.2 := by
      intro heq
      have heq' : a = b := Prod.ext hab heq
      exact hqa (by simpa only [heq', segment_same, mem_singleton_iff] using hq)
    let f : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ) := AffineEquiv.prodComm ℝ ℝ ℝ
    let s : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.prodComm ℝ ℝ
    have hmap (x : ℝ × ℝ) : s x ∈ segment ℝ (s a) (s b) ↔ x ∈ segment ℝ a b := by
      change f x ∈ segment ℝ (f a) (f b) ↔ x ∈ segment ℝ a b
      have hf : f '' segment ℝ a b = segment ℝ (f a) (f b) :=
        image_segment ℝ f.toAffineMap a b
      rw [← hf]
      exact f.injective.mem_set_image
    obtain ⟨e, he, hlocal⟩ := exists_local_line_of_nonvertical hab'
      ((hmap q).mpr hq) (s.injective.ne hqa) (s.injective.ne hqb)
    refine ⟨s.trans e, he, ?_⟩
    filter_upwards [(s.continuous.tendsto q).eventually hlocal] with x hx
    exact (hmap x).symm.trans hx
  · exact exists_local_line_of_nonvertical hab hq hqa hqb

end PlanarSegment
