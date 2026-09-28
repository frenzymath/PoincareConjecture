import PoincareConjecture.Proofs.M63.Mathlib.PrescribedPeriodicCurves
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicStepFlow
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTimeExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped ContDiff Topology Bundle

theorem exists_smooth_periodic_label_flow_on_prescribed_slab {L T0 S : ℝ}
    (hL : 0 < L) (hT0 : 0 < T0) (hS : 0 < S)
    (hST : S ≤ T0 / 4) (hS1 : S ≤ 1 / 2) (v : ℝ → ℝ → ℝ)
    (hper : ∀ t, Function.Periodic (v t) L)
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Ico 0 T0 ×ˢ univ)) :
    ∃ ψ : ℝ → ℝ → ℝ, (∀ x, ψ 0 x = x) ∧
      (∀ t ∈ Icc 0 S, ∀ x, ψ t (x + L) = ψ t x + L) ∧
      ContDiffOn ℝ ∞ (Function.uncurry ψ) (Icc 0 S ×ˢ univ) ∧
      (∀ t ∈ Icc 0 S, ∀ x,
        HasDerivWithinAt (fun s => ψ s x) (v t (ψ t x)) (Icc 0 S) t) ∧
      (∀ t ∈ Icc 0 S, ∀ x, 0 < deriv (ψ t) x) ∧
      ∀ t ∈ Icc 0 S, Function.Bijective (ψ t) := by
  obtain ⟨X, hX, hXper, hXv⟩ := exists_periodic_initialSlab_extension
    hL hT0 1 v hper (hv.of_le (by simp))
  let H := 2 * S
  have hH : 0 < H := by dsimp only [H]; positivity
  have hHT : H ≤ T0 / 2 := by dsimp only [H]; linarith
  have hH1 : H ≤ 1 := by dsimp only [H]; linarith
  have hSH : S < H := by dsimp only [H]; linarith
  obtain ⟨ψ, hψ0, hψt⟩ := exists_periodic_scalar_curves_on_Icc hL hH X hX hXper
  have hfinite (k : ℕ) :
      ContDiffOn ℝ (k + 1 : ℕ) (Function.uncurry ψ) (Icc 0 S ×ˢ univ) ∧
      (∀ t ∈ Icc 0 S, ∀ x, ψ t (x + L) = ψ t x + L) ∧
      (∀ t ∈ Icc 0 S, ∀ x, 0 < deriv (ψ t) x) ∧
      ∀ t ∈ Icc 0 S, Function.Bijective (ψ t) := by
    obtain ⟨Y, hY, hYper, hYv⟩ := exists_periodic_initialSlab_extension
      hL hT0 (k + 1) v hper
        (hv.of_le (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤)))
    obtain ⟨η, hη, B, hB0, hBt, hBper, hBsm, hBpos, hBbij⟩ :=
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
        (fun z : ℝ × ℝ => Q j z.1 z.2) (Icc 0 S ×ˢ univ) := by
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
          mem_univ _, hsmall ⟨hz.1.1, hz.1.2.trans_lt hSH⟩⟩
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
            s + r ∈ Icc 0 (T0 / 2) ∧ s + r ∈ Icc 0 H := by
          have hrH := hr.2.trans_le (min_le_right η (H - s))
          have hnonneg : 0 ≤ s + r := add_nonneg hs.1 hr.1
          exact ⟨⟨hnonneg, by linarith⟩, ⟨hnonneg, by linarith⟩⟩
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
            (((hasDerivAt_id r).const_add s).hasDerivWithinAt)
            (fun z hz => (htime hz).2)
          simp only [mul_one] at hd
          have hpair := (((hasDerivAt_id r).const_add s).hasDerivWithinAt).prodMk hd
          exact hpair.hasFDerivWithinAt.hasMFDerivWithinAt
        have hcompare :=
          PoincareConjecture.CompactTimeDependentFlowNative.isMIntegralCurveOn_Ico_eqOn
            hV hD hleft hright (by simp only [add_zero, hB0 s hsstart])
        have hdD : d ∈ Ico 0 D :=
          ⟨mul_nonneg hc ht.1, lt_min (hsmall ht).2 (by linarith)⟩
        change B s (Q j t x) d = ψ (((j + 1 : ℕ) : ℝ) * c * t) x
        rw [ih (Nat.le_of_succ_le hj) x]
        simpa only [s, d, Nat.cast_succ, add_mul, one_mul] using
          congrArg Prod.snd (hcompare hdD)
    have hQN (t : ℝ) (ht : t ∈ Icc 0 S) : Q N t = ψ t := by
      funext x
      simpa only [hNc, one_mul] using
        hQeq t ⟨ht.1, ht.2.trans_lt hSH⟩ N le_rfl x
    have hQgeom : ∀ j ≤ N, ∀ t ∈ Icc 0 S,
        (∀ x, Q j t (x + L) = Q j t x + L) ∧
        (∀ x, 0 < deriv (Q j t) x) ∧ Function.Bijective (Q j t) := by
      intro j
      induction j with
      | zero =>
        intro _ t _
        refine ⟨fun _ => rfl, ?_, Function.bijective_id⟩
        intro x
        change 0 < deriv (fun y : ℝ => y) x
        simp
      | succ j ih =>
        intro hj t ht
        have hprev := ih (Nat.le_of_succ_le hj) t ht
        have hb := hbounds ht.1 (Nat.le_of_succ_le hj)
        have hs : (j : ℝ) * c * t ∈ Ioo (-1 : ℝ) 1 :=
          ⟨by linarith [hb.1], by linarith [hb.2, ht.2]⟩
        have hd := hsmall ⟨ht.1, ht.2.trans_lt hSH⟩
        refine ⟨?_, ?_, (hBbij _ hs _ hd).comp hprev.2.2⟩
        · intro x
          change B ((j : ℝ) * c * t) (Q j t (x + L)) (c * t) =
            B ((j : ℝ) * c * t) (Q j t x) (c * t) + L
          rw [hprev.1 x]
          exact hBper _ hs _ _ hd
        · intro x
          have hpos := hBpos _ hs _ hd (Q j t x)
          have hdB := differentiableAt_of_deriv_ne_zero (ne_of_gt hpos)
          have hdQ := differentiableAt_of_deriv_ne_zero (ne_of_gt (hprev.2.1 x))
          change 0 < deriv ((fun y => B ((j : ℝ) * c * t) y (c * t)) ∘ Q j t) x
          rw [deriv_comp x hdB hdQ]
          exact mul_pos hpos (hprev.2.1 x)
    refine ⟨(hQsm N le_rfl).congr (fun z hz => ?_), ?_, ?_, ?_⟩
    · exact congrFun (hQN z.1 hz.1).symm z.2
    · intro t ht
      rw [← hQN t ht]
      exact (hQgeom N le_rfl t ht).1
    · intro t ht
      rw [← hQN t ht]
      exact (hQgeom N le_rfl t ht).2.1
    · intro t ht
      rw [← hQN t ht]
      exact (hQgeom N le_rfl t ht).2.2
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry ψ) (Icc 0 S ×ˢ univ) := by
    apply contDiffOn_infty.mpr
    intro k
    exact (hfinite k).1.of_le (by exact_mod_cast Nat.le_succ k)
  refine ⟨ψ, hψ0, (hfinite 0).2.1, hsmooth, ?_,
    (hfinite 0).2.2.1, (hfinite 0).2.2.2⟩
  intro t ht x
  have hd := hψt t ⟨ht.1, ht.2.trans hSH.le⟩ x
  rw [hXv t ⟨ht.1, by linarith [ht.2]⟩] at hd
  exact hd.mono (Icc_subset_Icc_right hSH.le)
