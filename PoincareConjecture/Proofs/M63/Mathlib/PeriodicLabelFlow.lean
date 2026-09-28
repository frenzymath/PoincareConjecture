import PoincareConjecture.Proofs.M63.Mathlib.PeriodicStepFlow
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTimeExtension










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped ContDiff Topology Bundle





theorem exists_smooth_periodic_label_flow {L T0 : ℝ}
    (hL : 0 < L) (hT0 : 0 < T0) (v : ℝ → ℝ → ℝ)
    (hper : ∀ t, Function.Periodic (v t) L)
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Ico 0 T0 ×ˢ univ)) :
    ∃ δ > 0, δ ≤ T0 / 4 ∧ δ ≤ 1 / 2 ∧ ∃ ψ : ℝ → ℝ → ℝ,
      (∀ x, ψ 0 x = x) ∧
      (∀ t ∈ Icc 0 δ, ∀ x, ψ t (x + L) = ψ t x + L) ∧
      ContDiffOn ℝ ∞ (Function.uncurry ψ) (Icc 0 δ ×ˢ univ) ∧
      (∀ t ∈ Icc 0 δ, ∀ x,
        HasDerivWithinAt (fun s => ψ s x) (v t (ψ t x)) (Icc 0 δ) t) ∧
      (∀ t ∈ Icc 0 δ, ∀ x, 0 < deriv (ψ t) x) ∧
      ∀ t ∈ Icc 0 δ, Function.Bijective (ψ t) := by
  obtain ⟨X, hX, hXper, hXv⟩ := exists_periodic_initialSlab_extension
    hL hT0 1 v hper (hv.of_le (by simp))
  obtain ⟨ε, hε, A, hA0, hAt, hAper, _hAsm, hApos, hAbij⟩ :=
    exists_periodic_step_flow hL (le_refl 1) X hX hXper
  let δ := min (ε / 4) (min (T0 / 4) (1 / 2))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδT : δ ≤ T0 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let H := 2 * δ
  have hH : 0 < H := by dsimp only [H]; positivity
  have hHT : H ≤ T0 / 2 := by dsimp only [H]; linarith
  have hH1 : H ≤ 1 := by dsimp only [H]; linarith
  have hHε : H < ε := by dsimp only [H]; linarith
  have hδH : δ < H := by dsimp only [H]; linarith
  have hstart : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  let ψ : ℝ → ℝ → ℝ := fun t x => A 0 x t
  have hψ0 (x : ℝ) : ψ 0 x = x := hA0 0 hstart x
  have hψt (t : ℝ) (ht : t ∈ Ioo (-ε) ε) (x : ℝ) :
      HasDerivAt (fun r => ψ r x) (X t (ψ t x)) t := by
    simpa only [ψ, zero_add] using hAt 0 hstart x t ht
  have hwindow {t : ℝ} (ht : t ∈ Icc 0 δ) : t ∈ Ioo (-ε) ε :=
    ⟨by linarith [ht.1], (ht.2.trans_lt hδH).trans hHε⟩
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry ψ) (Icc 0 δ ×ˢ univ) := by
    apply contDiffOn_infty.mpr
    intro k
    obtain ⟨Y, hY, hYper, hYv⟩ := exists_periodic_initialSlab_extension
      hL hT0 (k + 1) v hper
        (hv.of_le (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤)))
    obtain ⟨η, hη, B, hB0, hBt, _hBper, hBsm, _hBpos, _hBbij⟩ :=
      exists_periodic_step_flow hL (by omega : 1 ≤ k + 1) Y hY hYper
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt (half_pos hη)
    let N : ℕ := l + 1
    let c : ℝ := (N : ℝ)⁻¹
    have hN : 0 < (N : ℝ) := by dsimp only [N]; positivity
    have hc : 0 ≤ c := (inv_pos.mpr hN).le
    have hNc : (N : ℝ) * c = 1 := mul_inv_cancel₀ (ne_of_gt hN)
    have hcη : c < η / 2 := by
      simpa only [c, N, Nat.cast_add, Nat.cast_one, one_div] using hl
    have hbounds {t : ℝ} (ht : 0 ≤ t) {j : ℕ} (hj : j ≤ N) :
        0 ≤ (j : ℝ) * c * t ∧ (j : ℝ) * c * t ≤ t := by
      refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg j) hc) ht, ?_⟩
      calc
        (j : ℝ) * c * t = (j : ℝ) * (c * t) := mul_assoc _ _ _
        _ ≤ (N : ℝ) * (c * t) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (mul_nonneg hc ht)
        _ = t := by rw [← mul_assoc, hNc, one_mul]
    have hsmall {t : ℝ} (ht : t ∈ Ico 0 H) : c * t ∈ Ioo (-η) η := by
      have hct : c * t ≤ c := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (ht.2.le.trans hH1) hc
      exact ⟨by linarith [mul_nonneg hc ht.1], by linarith⟩
    let Q : ℕ → ℝ → ℝ → ℝ := Nat.rec (fun _ x => x)
      (fun j q t x => B ((j : ℝ) * c * t) (q t x) (c * t))
    have hQsm : ∀ j ≤ N, ContDiffOn ℝ (k + 1 : ℕ)
        (fun z : ℝ × ℝ => Q j z.1 z.2) (Icc 0 δ ×ˢ univ) := by
      intro j
      induction j with
      | zero => intro _; exact contDiffOn_snd
      | succ j ih =>
        intro hj
        have hjN := Nat.le_of_succ_le hj
        change ContDiffOn ℝ (k + 1 : ℕ)
          (fun z : ℝ × ℝ => B ((j : ℝ) * c * z.1) (Q j z.1 z.2) (c * z.1)) _
        apply hBsm.comp
          ((contDiffOn_const.mul contDiffOn_fst).prodMk
            ((ih hjN).prodMk (contDiffOn_const.mul contDiffOn_fst)))
        intro z hz
        have hb := hbounds hz.1.1 hjN
        exact ⟨⟨by linarith [hb.1], by linarith [hb.2, hz.1.2]⟩,
          mem_univ _, hsmall ⟨hz.1.1, hz.1.2.trans_lt hδH⟩⟩
    let V : ℝ × ℝ → ℝ × ℝ := fun p => (1, X p.1 p.2)
    have hV : ContMDiff 𝓘(ℝ, ℝ × ℝ)
        (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 1
        (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
      contMDiff_vectorSpace_iff_contDiff.mpr (contDiff_const.prodMk hX)
    have hQeq (t : ℝ) (ht : t ∈ Ico 0 H) :
        ∀ j ≤ N, ∀ x, Q j t x = ψ ((j : ℝ) * c * t) x := by
      intro j
      induction j with
      | zero =>
        intro _ x
        simpa only [Q, Nat.rec_zero, Nat.cast_zero, zero_mul] using (hψ0 x).symm
      | succ j ih =>
        intro hj x
        let s := (j : ℝ) * c * t
        let d := c * t
        have hs := hbounds ht.1 (Nat.le_of_succ_le hj)
        have hsd := hbounds ht.1 hj
        have hsH : s < H := hs.2.trans_lt ht.2
        have hsdH : s + d < H := by
          simpa only [s, d, Nat.cast_succ, add_mul, one_mul] using hsd.2.trans_lt ht.2
        have hsstart : s ∈ Ioo (-1 : ℝ) 1 :=
          ⟨by linarith [hs.1], hsH.trans_le hH1⟩
        let D := min η (H - s)
        have hD : 0 < D := lt_min hη (sub_pos.mpr hsH)
        have htime {r : ℝ} (hr : r ∈ Ico 0 D) :
            s + r ∈ Icc 0 (T0 / 2) ∧ s + r ∈ Ioo (-ε) ε := by
          have hrH := hr.2.trans_le (min_le_right η (H - s))
          have hnonneg : 0 ≤ s + r := add_nonneg hs.1 hr.1
          exact ⟨⟨hnonneg, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        have hleft : IsMIntegralCurveOn (I := 𝓘(ℝ, ℝ × ℝ))
            (fun r => (s + r, B s (ψ s x) r)) V (Ico 0 D) := by
          intro r hr
          have hrη : r ∈ Ioo (-η) η :=
            ⟨by linarith [hr.1], hr.2.trans_le (min_le_left _ _)⟩
          have hd := hBt s hsstart (ψ s x) r hrη
          rw [hYv (s + r) (htime hr).1, ← hXv (s + r) (htime hr).1] at hd
          have hpair := ((hasDerivAt_id r).const_add s).prodMk hd
          exact hpair.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
        have hright : IsMIntegralCurveOn (I := 𝓘(ℝ, ℝ × ℝ))
            (fun r => (s + r, ψ (s + r) x)) V (Ico 0 D) := by
          intro r hr
          have hd := (hψt (s + r) (htime hr).2 x).comp r
            ((hasDerivAt_id r).const_add s)
          simp only [mul_one] at hd
          have hpair := ((hasDerivAt_id r).const_add s).prodMk hd
          exact hpair.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
        have hcompare :=
          PoincareConjecture.CompactTimeDependentFlowNative.isMIntegralCurveOn_Ico_eqOn
            hV hD hleft hright (by simp only [add_zero, hB0 s hsstart])
        have hdD : d ∈ Ico 0 D :=
          ⟨mul_nonneg hc ht.1, lt_min (hsmall ht).2 (by linarith)⟩
        change B s (Q j t x) d = ψ (((j + 1 : ℕ) : ℝ) * c * t) x
        rw [ih (Nat.le_of_succ_le hj) x]
        simpa only [s, d, Nat.cast_succ, add_mul, one_mul] using
          congrArg Prod.snd (hcompare hdD)
    have hfinite : ContDiffOn ℝ (k + 1 : ℕ) (Function.uncurry ψ)
        (Icc 0 δ ×ˢ univ) := (hQsm N le_rfl).congr (by
      intro z hz
      simpa only [hNc, one_mul, Function.uncurry_def] using
        (hQeq z.1 ⟨hz.1.1, hz.1.2.trans_lt hδH⟩ N le_rfl z.2).symm)
    exact hfinite.of_le (by exact_mod_cast Nat.le_succ k)
  refine ⟨δ, hδ, hδT, hδ1, ψ, hψ0, ?_, hsmooth, ?_, ?_, ?_⟩
  · intro t ht x
    exact hAper 0 hstart x t (hwindow ht)
  · intro t ht x
    have hd := hψt t (hwindow ht) x
    rw [hXv t ⟨ht.1, by linarith [ht.2]⟩] at hd
    exact hd.hasDerivWithinAt
  · intro t ht x
    exact hApos 0 hstart t (hwindow ht) x
  · intro t ht
    exact hAbij 0 hstart t (hwindow ht)
