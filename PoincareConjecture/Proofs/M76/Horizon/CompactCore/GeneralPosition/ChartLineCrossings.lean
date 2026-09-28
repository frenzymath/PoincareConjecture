import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith










set_option autoImplicit false

open Set unitInterval

namespace AffineMap



theorem lineMap_zero_alternative {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ t : I, lineMap a b (t : ℝ) ≠ 0) ∨
      ∃ r : I, 0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧
        (r : ℝ) = a / (a - b) ∧
        ((a < 0 ∧ 0 < b) ∨ (b < 0 ∧ 0 < a)) ∧
        (∀ t : ℝ, lineMap a b t = 0 ↔ t = (r : ℝ)) ∧
        (∀ t : ℝ, t < r → 0 < a * lineMap a b t) ∧
        ∀ t : ℝ, (r : ℝ) < t → 0 < b * lineMap a b t := by
  classical
  by_cases hz : ∃ r : I, lineMap a b (r : ℝ) = 0
  · obtain ⟨r, hr⟩ := hz
    have hr0 : (r : ℝ) ≠ 0 := by
      intro h
      rw [h, lineMap_apply_zero] at hr
      exact ha hr
    have hr1 : (r : ℝ) ≠ 1 := by
      intro h
      rw [h, lineMap_apply_one] at hr
      exact hb hr
    have hrl : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1 hr0.symm
    have hru : (r : ℝ) < 1 := lt_of_le_of_ne r.property.2 hr1
    have heq : (1 - (r : ℝ)) * a + (r : ℝ) * b = 0 := by
      simpa only [lineMap_apply_ring] using hr
    have hop : (a < 0 ∧ 0 < b) ∨ (b < 0 ∧ 0 < a) := by
      rcases lt_or_gt_of_ne ha with ha | ha
      · left
        refine ⟨ha, ?_⟩
        by_contra h
        have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr hru) ha
        have hnonpos := mul_nonpos_of_nonneg_of_nonpos hrl.le (le_of_not_gt h)
        linarith
      · right
        refine ⟨?_, ha⟩
        by_contra h
        have hpos := mul_pos (sub_pos.mpr hru) ha
        have hnonneg := mul_nonneg hrl.le (le_of_not_gt h)
        linarith
    have hab : a ≠ b := by rcases hop with h | h <;> linarith
    have hfactor (t : ℝ) : lineMap a b t = (t - (r : ℝ)) * (b - a) := by
      rw [lineMap_apply_ring]
      nlinarith [heq]
    have hroot : (r : ℝ) = a / (a - b) := by
      apply (eq_div_iff (sub_ne_zero.mpr hab)).mpr
      nlinarith [heq]
    refine Or.inr ⟨r, hrl, hru, hroot, hop, ?_, ?_, ?_⟩
    · intro t
      rw [hfactor, mul_eq_zero, or_iff_left (sub_ne_zero.mpr hab.symm), sub_eq_zero]
    · intro t ht
      rw [hfactor]
      rcases hop with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact mul_pos_of_neg_of_neg ha
          (mul_neg_of_neg_of_pos (sub_neg.mpr ht) (by linarith))
      · exact mul_pos ha (mul_pos_of_neg_of_neg (sub_neg.mpr ht) (by linarith))
    · intro t ht
      rw [hfactor]
      rcases hop with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact mul_pos hb (mul_pos (sub_pos.mpr ht) (by linarith))
      · exact mul_pos_of_neg_of_neg hb
          (mul_neg_of_pos_of_neg (sub_pos.mpr ht) (by linarith))
  · exact Or.inl fun t ht => hz ⟨t, ht⟩

end AffineMap

namespace OpenPartialHomeomorph




theorem chart_line_frontier_alternative
    {X V : Type*} [TopologicalSpace X] [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    (B : OpenPartialHomeomorph X V) (f : I → X) {F : Set X}
    (hsource : ∀ t, f t ∈ B.source)
    (hline : ∀ t : I, B (f t) = AffineMap.lineMap (B (f 0)) (B (f 1)) (t : ℝ))
    (h0 : f 0 ∉ F) (h1 : f 1 ∉ F)
    (hchart : Disjoint B.source F ∨ ∃ ell : V →ᴬ[ℝ] ℝ,
      ∀ y ∈ B.source, y ∈ F ↔ ell (B y) = 0) :
    f ⁻¹' F = ∅ ∨ ∃ (r : I) (ell : V →ᴬ[ℝ] ℝ),
      0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧ f ⁻¹' F = {r} ∧
      (∀ y ∈ B.source, y ∈ F ↔ ell (B y) = 0) ∧
      (r : ℝ) = ell (B (f 0)) / (ell (B (f 0)) - ell (B (f 1))) ∧
      ((ell (B (f 0)) < 0 ∧ 0 < ell (B (f 1))) ∨
        (ell (B (f 1)) < 0 ∧ 0 < ell (B (f 0)))) ∧
      (∀ t : I, ell (B (f t)) = 0 ↔ t = r) ∧
      (∀ t : I, (t : ℝ) < r → 0 < ell (B (f 0)) * ell (B (f t))) ∧
      ∀ t : I, (r : ℝ) < t → 0 < ell (B (f 1)) * ell (B (f t)) := by
  rcases hchart with hdis | ⟨ell, hell⟩
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact disjoint_left.mp hdis (hsource t) ht
  · have hell0 : ell (B (f 0)) ≠ 0 := fun h => h0 ((hell _ (hsource 0)).mpr h)
    have hell1 : ell (B (f 1)) ≠ 0 := fun h => h1 ((hell _ (hsource 1)).mpr h)
    have hheight (t : I) : ell (B (f t)) =
        AffineMap.lineMap (ell (B (f 0))) (ell (B (f 1))) (t : ℝ) := by
      rw [hline]
      exact ell.toAffineMap.apply_lineMap _ _ _
    rcases AffineMap.lineMap_zero_alternative hell0 hell1 with hnone |
      ⟨r, hr0, hr1, hroot, hop, hzero, hbefore, hafter⟩
    · left
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hnone t ((hheight t).symm.trans ((hell _ (hsource t)).mp ht))
    · have hzero' (t : I) : ell (B (f t)) = 0 ↔ t = r := by
        rw [hheight, hzero]
        exact Subtype.val_injective.eq_iff
      have hpreimage : f ⁻¹' F = {r} := by
        ext t
        exact (hell _ (hsource t)).trans (hzero' t)
      refine Or.inr ⟨r, ell, hr0, hr1, hpreimage, hell, hroot, hop, hzero', ?_, ?_⟩
      · intro t ht
        rw [hheight t]
        exact hbefore t ht
      · intro t ht
        rw [hheight t]
        exact hafter t ht

end OpenPartialHomeomorph
