import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Maximum.CompactDomain














set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

theorem compact_subset_min_velocity_nonnegative_of_upper_support
    {M : Type u} [TopologicalSpace M] {C : Set M} (hC : IsCompact C)
    {T K : ℝ} (hT : 0 < T) (f : ℝ → M → ℝ)
    (hinit : ∀ x ∈ C, 0 ≤ f 0 x)
    (hboundary : ∀ t ∈ Icc 0 T, ∀ x ∈ C \ interior C, 0 ≤ f t x)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ C))
    (hsupport : ∀ t ∈ Ioc 0 T, ∀ x ∈ interior C,
      (∀ y ∈ C, f t x ≤ f t y) → f t x < 0 →
      ∀ δ > 0, ∃ ψ : ℝ → ℝ, ∃ v : ℝ,
        ψ t = f t x ∧
        (∀ᶠ s in 𝓝[Icc 0 t] t, f s x ≤ ψ s) ∧
        HasDerivWithinAt ψ v (Icc 0 t) t ∧
        -K * f t x - δ ≤ v) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ C, 0 ≤ f t x := by
  intro t ht x hx
  by_contra hbad
  have hbad' : f t x < 0 := lt_of_not_ge hbad
  let q := Real.exp (K * t) * f t x
  have hq : q < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) hbad'
  let ε := -q / (T + 1)
  have hε : 0 < ε := div_pos (neg_pos.mpr hq) (by linarith)
  have hεeq : ε * (T + 1) = -q :=
    div_mul_cancel₀ (-q) (ne_of_gt (by linarith : 0 < T + 1))
  let w : ℝ → M → ℝ := fun s y ↦ Real.exp (K * s) * f s y + ε * s
  have hwbad : w t x < 0 := by
    have hlt := mul_lt_mul_of_pos_left (show t < T + 1 by linarith [ht.2]) hε
    change q + ε * t < 0
    linarith
  let S : Set (ℝ × M) := Icc 0 t ×ˢ C
  have hsub : S ⊆ Icc 0 T ×ˢ C :=
    fun p hp ↦ ⟨⟨hp.1.1, hp.1.2.trans ht.2⟩, hp.2⟩
  have hwc : ContinuousOn (Function.uncurry w) S :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn.mul
      (hf.mono hsub)).add (continuous_const.mul continuous_fst).continuousOn
  obtain ⟨⟨s, y⟩, hsy, hminw⟩ := (isCompact_Icc.prod hC).exists_isMinOn
    (show S.Nonempty from ⟨(0, x), ⟨⟨le_rfl, ht.1⟩, hx⟩⟩) hwc
  change (s ∈ Icc 0 t) ∧ y ∈ C at hsy
  have hwy : w s y < 0 :=
    (hminw (show (t, x) ∈ S from ⟨⟨ht.1, le_rfl⟩, hx⟩)).trans_lt hwbad
  have hspos : 0 < s := by
    rcases lt_or_eq_of_le hsy.1.1 with hs | hs
    · exact hs
    · have hzero : w s y = f 0 y := by simp [w, ← hs]
      rw [hzero] at hwy
      exact False.elim ((not_lt_of_ge (hinit y hsy.2)) hwy)
  have hsJ : s ∈ Icc 0 T := ⟨hspos.le, hsy.1.2.trans ht.2⟩
  have hspace : ∀ z ∈ C, f s y ≤ f s z := by
    intro z hz
    have h := hminw (show (s, z) ∈ S from ⟨⟨hspos.le, hsy.1.2⟩, hz⟩)
    change Real.exp (K * s) * f s y + ε * s ≤
      Real.exp (K * s) * f s z + ε * s at h
    exact le_of_mul_le_mul_left (add_le_add_iff_right (ε * s) |>.mp h)
      (Real.exp_pos _)
  have hfneg : f s y < 0 := by
    by_contra h
    have hprod := mul_nonneg (Real.exp_pos (K * s)).le (le_of_not_gt h)
    have htime := mul_nonneg hε.le hspos.le
    change Real.exp (K * s) * f s y + ε * s < 0 at hwy
    linarith
  have hyint : y ∈ interior C := by
    by_contra hn
    exact (not_lt_of_ge (hboundary s hsJ y ⟨hsy.2, hn⟩)) hfneg
  obtain ⟨ψ, v, hψ, hψtime, hψderiv, hv⟩ :=
    hsupport s ⟨hspos, hsy.1.2.trans ht.2⟩ y
      hyint hspace hfneg (ε / (2 * Real.exp (K * s))) (by positivity)
  have htime : IsLocalMinOn
      (fun r ↦ Real.exp (K * r) * ψ r + ε * r) (Icc 0 s) s := by
    rw [IsLocalMinOn]
    filter_upwards [hψtime, self_mem_nhdsWithin] with r hr hrs
    have hmin := hminw (show (r, y) ∈ S from
      ⟨⟨hrs.1, hrs.2.trans hsy.1.2⟩, hsy.2⟩)
    have hle : Real.exp (K * r) * f r y + ε * r ≤
        Real.exp (K * r) * ψ r + ε * r := by
      have := mul_le_mul_of_nonneg_left hr (Real.exp_pos (K * r)).le
      linarith
    calc
      Real.exp (K * s) * ψ s + ε * s =
          Real.exp (K * s) * f s y + ε * s := by rw [hψ]
      _ ≤ Real.exp (K * r) * f r y + ε * r := hmin
      _ ≤ Real.exp (K * r) * ψ r + ε * r := hle
  have hcone : 0 - s ∈ posTangentConeAt (Icc 0 s) s :=
    sub_mem_posTangentConeAt_of_segment_subset
      (by rw [segment_symm, segment_eq_Icc hspos.le])
  have hdexp : HasDerivAt (fun r : ℝ ↦ Real.exp (K * r))
      (Real.exp (K * s) * K) s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul K).exp
  have hde : HasDerivWithinAt (fun r : ℝ ↦ ε * r) ε (Icc 0 s) s := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id s).const_mul ε).hasDerivWithinAt)
  have hdw : HasDerivWithinAt
      (fun r ↦ Real.exp (K * r) * ψ r + ε * r)
      (Real.exp (K * s) * (v + K * ψ s) + ε) (Icc 0 s) s := by
    convert! (hdexp.hasDerivWithinAt.mul hψderiv).add hde using 1
    ring
  have hsign : 0 ≤ (0 - s) *
      (Real.exp (K * s) * (v + K * ψ s) + ε) := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      using htime.hasFDerivWithinAt_nonneg hdw hcone
  have he : 0 < Real.exp (K * s) := Real.exp_pos _
  have hsum : 0 < v + K * f s y + ε / Real.exp (K * s) := by
    have hle : ε / (2 * Real.exp (K * s)) ≤
        v + K * f s y + ε / Real.exp (K * s) := by
      calc
        ε / (2 * Real.exp (K * s)) =
            (-K * f s y - ε / (2 * Real.exp (K * s))) +
              (K * f s y + ε / Real.exp (K * s)) := by
                field_simp [ne_of_gt he]
                ring
        _ ≤ v + K * f s y + ε / Real.exp (K * s) := by
          nlinarith [hv]
    exact lt_of_lt_of_le (by positivity) hle
  have hpos : 0 < Real.exp (K * s) * (v + K * ψ s) + ε := by
    rw [hψ]
    have heq : Real.exp (K * s) * (v + K * f s y) + ε =
        Real.exp (K * s) * (v + K * f s y + ε / Real.exp (K * s)) := by
      field_simp [ne_of_gt he]
    rw [heq]
    exact mul_pos he hsum
  exact (not_lt_of_ge hsign)
    (mul_neg_of_neg_of_pos (sub_neg.mpr hspos) hpos)

end PoincareConjecture.RicciFlowAnalysis
