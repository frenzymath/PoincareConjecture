import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp













set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Parabolic

private lemma nonneg_deriv_of_local_max_on_past {f : ℝ → ℝ} {d a t : ℝ}
    (hat : a < t) (hmax : IsLocalMaxOn f (Icc a t) t)
    (hd : HasDerivAt f d t) : 0 ≤ d := by
  have hcone : a - t ∈ posTangentConeAt (Icc a t) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a t).segment_subset ⟨hat.le, le_rfl⟩ ⟨le_rfl, hat.le⟩)
  have h := hmax.hasFDerivWithinAt_nonpos hd.hasDerivWithinAt.hasFDerivWithinAt hcone
  change (a - t) * d ≤ 0 at h
  nlinarith




theorem le_exp_of_lower_support_deriv_le
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {u : A → ℝ → ℝ} {K B U0 a b : ℝ}
    (hK : 0 < K) (hB : 0 ≤ B) (hU0 : 0 ≤ U0)
    (hu : ContinuousOn (Function.uncurry u) (univ ×ˢ Icc a b))
    (hinit : ∀ q, u q a ≤ U0)
    (hsupport : ∀ (rate : ℝ) (q : A) (t : ℝ),
      K < rate → t ∈ Ioc a b → 0 < u q t →
      IsMaxOn
        (fun p : A × ℝ => Real.exp (-rate * (p.2 - a)) * (u p.1 p.2 + B / K))
        (univ ×ˢ Icc a b) (q, t) →
      ∃ (v : ℝ → ℝ) (d : ℝ),
        v t = u q t ∧
        (∀ᶠ s in 𝓝[Icc a t] t, v s ≤ u q s) ∧
        HasDerivAt v d t ∧ d ≤ K * u q t + B) :
    ∀ q t, t ∈ Icc a b →
      u q t ≤ Real.exp (K * (t - a)) * (U0 + B / K) - B / K := by
  have hC : 0 ≤ U0 + B / K := add_nonneg hU0 (div_nonneg hB hK.le)
  have hweighted (rate : ℝ) (hrate : K < rate) (q : A) (t : ℝ)
      (ht : t ∈ Icc a b) :
      Real.exp (-rate * (t - a)) * (u q t + B / K) ≤ U0 + B / K := by
    by_contra hle
    have hlt := lt_of_not_ge hle
    let G : A × ℝ → ℝ := fun p =>
      Real.exp (-rate * (p.2 - a)) * (u p.1 p.2 + B / K)
    have hG : ContinuousOn G (univ ×ˢ Icc a b) :=
      (show Continuous (fun p : A × ℝ => Real.exp (-rate * (p.2 - a))) by
        fun_prop).continuousOn.mul (hu.add continuousOn_const)
    obtain ⟨⟨p, s⟩, hs, hmax⟩ :=
      (isCompact_univ.prod isCompact_Icc).exists_isMaxOn ⟨(q, t), trivial, ht⟩ hG
    have hGs : U0 + B / K < G (p, s) :=
      hlt.trans_le (hmax (a := (q, t)) ⟨trivial, ht⟩)
    have hshift : 0 < u p s + B / K :=
      (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (hC.trans_lt hGs)
    have hexple : Real.exp (-rate * (s - a)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (hK.trans hrate).le) (sub_nonneg.mpr hs.2.1))
    have hpos : 0 < u p s := by
      have hmul := mul_le_of_le_one_left hshift.le hexple
      dsimp only [G] at hGs
      linarith
    have has : a < s := lt_of_le_of_ne hs.2.1 (by
      intro heq
      subst s
      have hGa : U0 + B / K < u p a + B / K := by simpa [G] using hGs
      linarith [hinit p])
    obtain ⟨v, d, htouch, hbelow, hd, hreaction⟩ :=
      hsupport rate p s hrate ⟨has, hs.2.2⟩ hpos hmax
    let w : ℝ → ℝ := fun r => Real.exp (-rate * (r - a)) * (v r + B / K)
    have hlocal : IsLocalMaxOn w (Icc a s) s := by
      filter_upwards [hbelow, self_mem_nhdsWithin] with r hr hmem
      calc
        w r ≤ G (p, r) :=
          mul_le_mul_of_nonneg_left (by linarith : v r + B / K ≤ u p r + B / K)
            (Real.exp_pos _).le
        _ ≤ G (p, s) := hmax ⟨trivial, hmem.1, hmem.2.trans hs.2.2⟩
        _ = w s := by simp only [G, w, htouch]
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (-rate * (r - a)))
        (Real.exp (-rate * (s - a)) * (-rate)) s := by
      simpa [id_eq] using (((hasDerivAt_id s).sub_const a).const_mul (-rate)).exp
    have hnonneg := nonneg_deriv_of_local_max_on_past has hlocal
      (hexp.mul (hd.add_const (B / K)))
    rw [htouch] at hnonneg
    have hBK : K * (B / K) = B := mul_div_cancel₀ B hK.ne'
    have hstrict : d - rate * (u p s + B / K) < 0 := by
      nlinarith [mul_pos (sub_pos.mpr hrate) hshift]
    nlinarith [mul_neg_of_pos_of_neg (Real.exp_pos (-rate * (s - a))) hstrict]
  intro q t ht
  have hlim : Tendsto
      (fun rate : ℝ => Real.exp (-rate * (t - a)) * (u q t + B / K))
      (𝓝[>] K) (𝓝 (Real.exp (-K * (t - a)) * (u q t + B / K))) :=
    (by fun_prop : Continuous (fun rate : ℝ =>
      Real.exp (-rate * (t - a)) * (u q t + B / K))).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have hbound := le_of_tendsto hlim
    ((show ∀ᶠ rate in 𝓝[>] K, K < rate from self_mem_nhdsWithin).mono
      fun rate hrate => hweighted rate hrate q t ht)
  have hdiv := (le_div_iff₀ (Real.exp_pos (-K * (t - a)))).mpr
    (by simpa only [mul_comm] using hbound)
  rw [neg_mul, Real.exp_neg, div_inv_eq_mul] at hdiv
  nlinarith

end Poincare.Parabolic
