import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PeriodicFirstContact
import Mathlib.Analysis.SpecialFunctions.Complex.Circle













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff

namespace PoincareConjecture




theorem m64Intrinsic_inner_boundary_injOn_period :
    InjOn (intrinsicAnnulusBoundary 1) (Ico (0 : ℝ) rampPeriod) := by
  intro x hx y hy hxy
  apply Circle.exp_injOn_Ico (by simp [rampPeriod]) hx hy
  apply Subtype.ext
  apply Complex.ext
  · have h := congrArg (fun z : AnnulusCoordinates => z 0) hxy
    simp only [intrinsicAnnulusBoundary, one_mul, Matrix.cons_val_zero] at h
    simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using h
  · have h := congrArg (fun z : AnnulusCoordinates => z 1) hxy
    simp only [intrinsicAnnulusBoundary, one_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h
    simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using h




theorem m64Intrinsic_normal_collision_heights_pos
    {u : ℝ × ℝ → AnnulusCoordinates} {T : ℝ}
    (hboundary : ∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a)
    (hinside : ∀ a ∈ Ico (0 : ℝ) rampPeriod, ∀ t ∈ Ioc (0 : ℝ) T,
      1 < ‖u (a, t)‖)
    {p q : ℝ × ℝ}
    (hp : p ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T)
    (hq : q ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T)
    (hne : p ≠ q) (hmeet : u p = u q) : 0 < p.2 ∧ 0 < q.2 := by
  have hnorm (a : ℝ) : ‖u (a, 0)‖ = 1 := by
    rw [hboundary]
    have h := m64Intrinsic_boundary_self_inner 1 a
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 a)]
  have hzero (a b t : ℝ) (ha : a ∈ Ico (0 : ℝ) rampPeriod)
      (hb : b ∈ Ico (0 : ℝ) rampPeriod) (ht : t ∈ Icc (0 : ℝ) T)
      (heq : u (a, 0) = u (b, t)) : a = b ∧ t = 0 := by
    have ht0 : t = 0 := by
      by_contra hne
      have hlt := hinside b hb t ⟨lt_of_le_of_ne ht.1 (Ne.symm hne), ht.2⟩
      rw [← heq, hnorm] at hlt
      exact (lt_irrefl (1 : ℝ)) hlt
    refine ⟨m64Intrinsic_inner_boundary_injOn_period ha hb ?_, ht0⟩
    simpa only [ht0, hboundary] using heq
  have hpositive (r s : ℝ × ℝ)
      (hr : r ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T)
      (hs : s ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T)
      (hne : r ≠ s) (heq : u r = u s) : 0 < r.2 := by
    by_contra hnot
    have hr0 : r.2 = 0 := le_antisymm (le_of_not_gt hnot) hr.2.1
    have hz := hzero r.1 s.1 s.2 hr.1 hs.1 hs.2 (by simpa only [← hr0] using heq)
    exact hne (Prod.ext hz.1 (hr0.trans hz.2.symm))
  exact ⟨hpositive p q hp hq hne hmeet, hpositive q p hq hp hne.symm hmeet.symm⟩

end PoincareConjecture
