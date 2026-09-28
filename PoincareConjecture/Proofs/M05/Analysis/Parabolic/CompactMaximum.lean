import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

set_option autoImplicit false

open Set
open scoped Topology

namespace Poincare.Parabolic

private lemma nonneg_deriv_of_max_on_interval {f : ℝ → ℝ} {f' a b t : ℝ}
    (ht : t ∈ Ioc a b) (hmax : IsMaxOn f (Icc a b) t)
    (hd : HasDerivWithinAt f f' (Icc a b) t) : 0 ≤ f' := by
  have hcone : a - t ∈ posTangentConeAt (Icc a b) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset ⟨ht.1.le, ht.2⟩ ⟨le_rfl, ht.1.le.trans ht.2⟩)
  have h := hmax.localize.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt hcone
  change (a - t) * f' ≤ 0 at h
  nlinarith [ht.1]

theorem nonpos_of_deriv_le_mul_at_max
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {F F' : A → ℝ → ℝ} {K a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hderiv : ∀ q t, t ∈ Ioc a b →
      HasDerivWithinAt (F q) (F' q t) (Icc a b) t)
    (hmax : ∀ q t, t ∈ Ioc a b → 0 < F q t →
      (∀ p, F p t ≤ F q t) → F' q t ≤ K * F q t)
    (hinit : ∀ q, F q a ≤ 0) :
    ∀ q t, t ∈ Icc a b → F q t ≤ 0 := by
  intro q t ht
  by_contra hnonpos
  have hpos : 0 < F q t := lt_of_not_ge hnonpos
  let G : A × ℝ → ℝ := fun p => Real.exp (-(K + 1) * (p.2 - a)) * F p.1 p.2
  have hG : ContinuousOn G (univ ×ˢ Icc a b) :=
    (show Continuous (fun p : A × ℝ => Real.exp (-(K + 1) * (p.2 - a))) by
      fun_prop).continuousOn.mul hF
  obtain ⟨⟨p, s⟩, hs, hps⟩ :=
    (isCompact_univ.prod isCompact_Icc).exists_isMaxOn ⟨(q, t), trivial, ht⟩ hG
  have hpsqt : G (q, t) ≤ G (p, s) := hps ⟨trivial, ht⟩
  have hGs : 0 < G (p, s) :=
    (mul_pos (Real.exp_pos _) hpos).trans_le hpsqt
  have hFs : 0 < F p s := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hGs
  have has : a < s := lt_of_le_of_ne hs.2.1 (by
    intro heq
    subst s
    exact (not_lt_of_ge (hinit p)) hFs)
  have hs' : s ∈ Ioc a b := ⟨has, hs.2.2⟩
  have hspace : ∀ r, F r s ≤ F p s := by
    intro r
    have h := hps (a := (r, s)) ⟨trivial, hs.2⟩
    change G (r, s) ≤ G (p, s) at h
    exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp h
  have htime : IsMaxOn (fun r => G (p, r)) (Icc a b) s :=
    fun r hr => hps (a := (p, r)) ⟨trivial, hr⟩
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-(K + 1) * (r - a)))
      (Real.exp (-(K + 1) * (s - a)) * (-(K + 1))) s :=
    by simpa [id_eq] using (((hasDerivAt_id s).sub_const a).const_mul (-(K + 1))).exp
  have hd := hexp.hasDerivWithinAt.mul (hderiv p s hs')
  have hge := nonneg_deriv_of_max_on_interval hs' htime hd
  have hle := hmax p s hs' hFs hspace
  have hexppos := Real.exp_pos (-(K + 1) * (s - a))
  nlinarith

end Poincare.Parabolic
