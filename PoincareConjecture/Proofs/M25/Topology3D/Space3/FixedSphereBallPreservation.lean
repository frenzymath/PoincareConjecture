import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E]



theorem fixedSphere_isotopy_norm_sides (Φ : ℝ → E ≃ₜ E)
    (hc : ∀ x, ContinuousOn (fun t => Φ t x) (Icc (0 : ℝ) 1))
    (hzero : ∀ x, Φ 0 x = x)
    (hfixed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ = 1 → Φ t x = x)
    {t : ℝ} (ht : t ∈ Icc 0 1) (x : E) :
    (‖Φ t x‖ < 1 ↔ ‖x‖ < 1) ∧ (‖Φ t x‖ ≤ 1 ↔ ‖x‖ ≤ 1) := by
  have hone (s : ℝ) (hs : s ∈ Icc 0 1) : ‖Φ s x‖ = 1 ↔ ‖x‖ = 1 := by
    constructor
    · intro hx
      have heq : Φ s x = x := (Φ s).injective (hfixed s hs (Φ s x) hx)
      simpa only [heq] using hx
    · intro hx
      rw [hfixed s hs x hx, hx]
  have hpath : ContinuousOn (fun s => ‖Φ s x‖) (Icc 0 t) :=
    (hc x).norm.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
  have hlt (hx : ‖x‖ < 1) : ‖Φ t x‖ < 1 := by
    by_contra h
    obtain ⟨s, hs, heq⟩ := intermediate_value_Icc ht.1 hpath
      (show (1 : ℝ) ∈ Icc ‖Φ 0 x‖ ‖Φ t x‖ from ⟨by simpa only [hzero] using hx.le,
        le_of_not_gt h⟩)
    exact hx.ne ((hone s ⟨hs.1, hs.2.trans ht.2⟩).mp heq)
  have hgt (hx : 1 < ‖x‖) : 1 < ‖Φ t x‖ := by
    by_contra h
    obtain ⟨s, hs, heq⟩ := intermediate_value_Icc' ht.1 hpath
      (show (1 : ℝ) ∈ Icc ‖Φ t x‖ ‖Φ 0 x‖ from ⟨le_of_not_gt h,
        by simpa only [hzero] using hx.le⟩)
    exact hx.ne' ((hone s ⟨hs.1, hs.2.trans ht.2⟩).mp heq)
  constructor
  · constructor
    · intro hy
      rcases lt_trichotomy ‖x‖ 1 with hx | hx | hx
      · exact hx
      · exact (hy.ne ((hone t ht).mpr hx)).elim
      · exact (not_lt_of_gt (hgt hx) hy).elim
    · exact hlt
  · constructor
    · intro hy
      by_contra hx
      exact (not_lt_of_ge hy) (hgt (lt_of_not_ge hx))
    · intro hx
      rcases hx.lt_or_eq with hl | he
      · exact (hlt hl).le
      · exact ((hone t ht).mpr he).le



theorem fixedSphere_isotopy_image_balls (Φ : ℝ → E ≃ₜ E)
    (hc : ∀ x, ContinuousOn (fun t => Φ t x) (Icc (0 : ℝ) 1))
    (hzero : ∀ x, Φ 0 x = x)
    (hfixed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ = 1 → Φ t x = x)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    Φ t '' ball (0 : E) 1 = ball 0 1 ∧
      Φ t '' closedBall (0 : E) 1 = closedBall 0 1 := by
  have hs := fixedSphere_isotopy_norm_sides Φ hc hzero hfixed ht
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_ball_zero_iff.mpr ((hs x).1.mpr (mem_ball_zero_iff.mp hx))
    · intro hy
      refine ⟨(Φ t).symm y, ?_, (Φ t).apply_symm_apply y⟩
      apply mem_ball_zero_iff.mpr
      apply (hs ((Φ t).symm y)).1.mp
      simpa only [(Φ t).apply_symm_apply] using mem_ball_zero_iff.mp hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_closedBall_zero_iff.mpr ((hs x).2.mpr (mem_closedBall_zero_iff.mp hx))
    · intro hy
      refine ⟨(Φ t).symm y, ?_, (Φ t).apply_symm_apply y⟩
      apply mem_closedBall_zero_iff.mpr
      apply (hs ((Φ t).symm y)).2.mp
      simpa only [(Φ t).apply_symm_apply] using mem_closedBall_zero_iff.mp hy

end PoincareConjecture.M25.Topology3D
