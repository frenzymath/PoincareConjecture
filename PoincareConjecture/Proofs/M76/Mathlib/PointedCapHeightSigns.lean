import PoincareConjecture.Proofs.M76.Mathlib.VariableBandHeightSigns










set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]






theorem pointed_cap_mem_both_height_closures
    {s d b B T : Set E} (H : E ≃ₜ E) (A r : E → ℝ)
    {t : ℝ} (ht : 0 < t)
    (hheight : ∀ x ∈ d, A (H x) = t * r x)
    (hrange : ∀ x ∈ d, r x ≤ 2)
    (hmax : ∀ x ∈ d, r x = 2 → x ∈ b)
    (hlower : ∀ x ∈ d, 0 < r x → x ∈ closure (d ∩ {y | r y < r x}))
    (hupper : ∀ x ∈ d, r x < 2 → x ∈ closure (d ∩ {y | r x < r y}))
    {lower upper : E → ℝ}
    (D : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} ≃ₜ T)
    (hDA : ∀ p, A (D p) = (p : E × ℝ).2)
    (hT : T ⊆ H '' (s ∪ d))
    (hrim : ∀ x ∈ b, 0 < r x →
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)},
        (D p : E) = H x ∧ (p : E × ℝ).2 < upper (p : E × ℝ).1) :
    ∀ x ∈ H '' d, 0 < A x →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  rintro _ ⟨x, hxd, rfl⟩ hxA
  have hrpos : 0 < r x := by
    have h := hxA
    rw [hheight x hxd] at h
    exact (mul_pos_iff_of_pos_left ht).mp h
  refine ⟨?_, ?_⟩
  · apply H.continuous.continuousWithinAt.mem_closure (hlower x hxd hrpos)
    intro y hy
    refine ⟨⟨y, Or.inr hy.1, rfl⟩, ?_⟩
    change A (H y) < A (H x)
    rw [hheight y hy.1, hheight x hxd]
    exact mul_lt_mul_of_pos_left hy.2 ht
  · by_cases hrlt : r x < 2
    · apply H.continuous.continuousWithinAt.mem_closure (hupper x hxd hrlt)
      intro y hy
      refine ⟨⟨y, Or.inr hy.1, rfl⟩, ?_⟩
      change A (H x) < A (H y)
      rw [hheight x hxd, hheight y hy.1]
      exact mul_lt_mul_of_pos_left hy.2 ht
    · have hreq : r x = 2 := le_antisymm (hrange x hxd) (le_of_not_gt hrlt)
      obtain ⟨p, hp, hphi⟩ := hrim x (hmax x hxd hreq) hrpos
      have h := closure_mono (inter_subset_inter_left _ hT)
        ((D.mem_height_closures_of_variableBand A hDA p).2 hphi)
      rwa [hp] at h

end Homeomorph
