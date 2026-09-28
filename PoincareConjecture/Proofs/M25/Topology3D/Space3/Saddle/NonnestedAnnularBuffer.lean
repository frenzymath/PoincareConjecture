import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.AngularReconnection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CrosscutFilledCells
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in

theorem exists_saddle_nonnested_annular_buffer
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (mu : Fin 2 → ℝ) (hmu : ∀ j, 0 < mu j)
    (hmuSmall : ∀ j, mu j ≤ 1 / 128)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let F : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
      fun j => Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 (mu j) (hmu j) (hmuSmall j) chi hchi
        hchiBounds hchiSupport hchiOne)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let K := kappa '' closedBall (0 : E2) 1
    let sign : Fin 2 → ℝ := ![1, -1]
    let Z : Fin 2 → Fin 2 → Set E2 := fun j i =>
      {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu j)}
    let Short : Fin 2 → Fin 2 → Set E2 := fun j i =>
      {x | ‖x‖ ≤ 1 ∧ Real.sqrt ((J2 x).1 ^ 2 + mu j) < sign i * (J2 x).2}
    let Long : Fin 2 → Fin 2 → Set E2 := fun j i =>
      {x | ‖x‖ ≤ 1 ∧ sign i * (J2 x).2 < Real.sqrt ((J2 x).1 ^ 2 + mu j)}
    let Eta : Fin 2 → Fin 2 → Set E2 := fun j i =>
      kappa '' ((F j 1) '' Z j i)
    ∀ (nu : ℝ) (hnu : 0 < nu) (hnuSmall : nu < 1 / 16)
      (alpha : Fin 2 → Fin 2 → ℝ → E2)
      (hAlpha : ∀ j i,
        ContDiffOn ℝ ∞ (alpha j i) (Ioo (-nu) (1 + nu)))
      (hProper : ∀ j i, alpha j i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ)
      (hInitial : ∀ j i t, |t| < nu →
        alpha j i t = kappa ((1 + t) • port (ep (i, 0))))
      (hTerminal : ∀ j i t, |t - 1| < nu →
        alpha j i t = kappa ((2 - t) • port (ep (i, 1))))
      (B : Fin 2 → Fin 2 → BallNeighborhoodChart E2 E2)
      (hBoundary : ∀ j i,
        (B j i).boundary = (alpha j i '' Icc (0 : ℝ) 1) ∪ Eta j i)
      (hCase : ∀ j, Disjoint (B j 0).closedRegion (B j 1).closedRegion),
      ∃ h : ℝ,
        0 < h ∧ h < nu / 128 ∧ h < 1 / 1024 ∧
        (∀ j i,
          kappa '' ((F j 1) '' Short j i) ⊆ (B j i).inside ∧
          kappa '' ((F j 1) '' Long j i) ⊆ (B j i).closedRegionᶜ ∧
          kappa (0 : E2) ∉ (B j i).closedRegion) ∧
        (∀ j i,
          (alpha j i '' Icc (0 : ℝ) 1) ∩
              (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
            kappa '' (((fun r : ℝ => r • port (ep (i, 0))) '' Icc 1 (1 + 32 * h)) ∪
              ((fun r : ℝ => r • port (ep (i, 1))) '' Icc 1 (1 + 32 * h)))) ∧
        (∀ j i,
          kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
              |(J2 x).1| < sign i * (J2 x).2} ⊆ (B j i).inside) ∧
        ∀ j i,
          kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
              |(J2 x).1| ≤ sign i * (J2 x).2} ⊆ (B j i).closedRegion := by
  classical
  let F : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    fun j => Classical.choose (exists_saddle_angular_reconnection
      J2 hJ2 (mu j) (hmu j) (hmuSmall j) chi hchi
      hchiBounds hchiSupport hchiOne)
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun a => J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let K := kappa '' closedBall (0 : E2) 1
  let sign : Fin 2 → ℝ := ![1, -1]
  let Z : Fin 2 → Fin 2 → Set E2 := fun j i =>
    {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu j)}
  let Short : Fin 2 → Fin 2 → Set E2 := fun j i =>
    {x | ‖x‖ ≤ 1 ∧ Real.sqrt ((J2 x).1 ^ 2 + mu j) < sign i * (J2 x).2}
  let Long : Fin 2 → Fin 2 → Set E2 := fun j i =>
    {x | ‖x‖ ≤ 1 ∧ sign i * (J2 x).2 < Real.sqrt ((J2 x).1 ^ 2 + mu j)}
  let Eta : Fin 2 → Fin 2 → Set E2 := fun j i => kappa '' ((F j 1) '' Z j i)
  dsimp only
  intro nu hnu hnuSmall alpha hAlpha hProper hInitial hTerminal B hBoundary hCase
  change ∀ j i, alpha j i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ at hProper
  change ∀ j i t, |t| < nu → alpha j i t = kappa ((1 + t) • port (ep (i, 0))) at hInitial
  change ∀ j i t, |t - 1| < nu → alpha j i t = kappa ((2 - t) • port (ep (i, 1))) at hTerminal
  change ∀ j i, (B j i).boundary = (alpha j i '' Icc (0 : ℝ) 1) ∪ Eta j i at hBoundary
  have hFs (j : Fin 2) := Classical.choose_spec (exists_saddle_angular_reconnection
    J2 hJ2 (mu j) (hmu j) (hmuSmall j) chi hchi hchiBounds hchiSupport hchiOne)
  have hFn (j : Fin 2) (x : E2) : ‖F j 1 x‖ = ‖x‖ ∧ ‖(F j 1).symm x‖ = ‖x‖ :=
    (hFs j).2.2.2.1 1 x
  have hs (i : Fin 2) : (sign i) ^ 2 = 1 := by fin_cases i <;> norm_num [sign]
  have hsrc {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ kappa.source :=
    hkappaSource (by simpa only [mem_closedBall, dist_zero_right] using hx)
  have hnorm (x y : ℝ) : ‖J2.symm (x, y)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    simpa only [J2.apply_symm_apply] using (hJ2 (J2.symm (x, y))).symm
  have hSigns (a : Fin 4) : (sx a) ^ 2 = 1 ∧ (sy a) ^ 2 = 1 := by
    fin_cases a <;> norm_num [sx, sy]
  have hportN (a : Fin 4) : ‖port a‖ = 1 := by
    have hh := hnorm (sx a / Real.sqrt 2) (sy a / Real.sqrt 2)
    change ‖port a‖ ^ 2 = _ at hh
    rw [div_pow, div_pow, (hSigns a).1, (hSigns a).2,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hh
    nlinarith [norm_nonneg (port a)]
  have hportCone (i e : Fin 2) (r : ℝ) (hr : 0 ≤ r) :
      |(J2 (r • port (ep (i, e)))).1| = sign i * (J2 (r • port (ep (i, e)))).2 := by
    have hsq : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    fin_cases i <;> fin_cases e <;>
      simp [port, ep, finProdFinEquiv, sx, sy, sign, map_smul,
        abs_mul, abs_div, abs_of_nonneg hr, abs_of_nonneg hsq] <;> ring
  let old : Fin 2 → Fin 2 → Fin 2 → E2 := fun j i e => J2.symm
    (sx (ep (i, e)) * Real.sqrt ((1 - mu j) / 2),
      sy (ep (i, e)) * Real.sqrt ((1 + mu j) / 2))
  have hold (j i e : Fin 2) : old j i e ∈ Z j i ∧ F j 1 (old j i e) = port (ep (i, e)) := by
    have ha : 0 ≤ (1 - mu j) / 2 := by linarith [hmuSmall j]
    have hb : 0 ≤ (1 + mu j) / 2 := by linarith [hmu j]
    have hc : Real.sqrt (((1 - mu j) / 2) + mu j) = Real.sqrt ((1 + mu j) / 2) := by congr 1; ring
    have hn : ‖old j i e‖ = 1 := by
      have hn := hnorm (sx (ep (i, e)) * Real.sqrt ((1 - mu j) / 2))
        (sy (ep (i, e)) * Real.sqrt ((1 + mu j) / 2))
      change ‖old j i e‖ ^ 2 = _ at hn
      rw [mul_pow, mul_pow, (hSigns (ep (i, e))).1, (hSigns (ep (i, e))).2,
        Real.sq_sqrt ha, Real.sq_sqrt hb, one_mul, one_mul] at hn
      nlinarith [norm_nonneg (old j i e)]
    refine ⟨⟨hn.le, ?_⟩, ?_⟩
    · simp only [old, J2.apply_symm_apply]
      rw [mul_pow, (hSigns (ep (i, e))).1, one_mul, Real.sq_sqrt ha, hc]
      congr 1
      fin_cases i <;> fin_cases e <;> norm_num [sy, sign, ep, finProdFinEquiv]
    · have he := (hFs j).2.2.2.2.2.2.2.2.1 1 (ep (i, e)) 1 (by constructor <;> norm_num)
      change F j 1 (J2.symm
        (sx (ep (i, e)) * Real.sqrt ((1 ^ 2 + -mu j) / 2),
          sy (ep (i, e)) * Real.sqrt ((1 ^ 2 - -mu j) / 2))) =
        J2.symm (sx (ep (i, e)) * Real.sqrt ((1 ^ 2 + -(1 - Real.smoothTransition 1) * mu j) / 2),
          sy (ep (i, e)) * Real.sqrt ((1 ^ 2 - -(1 - Real.smoothTransition 1) * mu j) / 2)) at he
      have hhalf : Real.sqrt ((1 : ℝ) / 2) = 1 / Real.sqrt 2 := by
        rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
      simp only [Real.smoothTransition.one, sub_self, neg_zero, zero_mul, one_pow,
        add_zero, sub_zero, ← sub_eq_add_neg, sub_neg_eq_add] at he
      rw [hhalf] at he
      simpa only [old, port, div_eq_mul_inv, one_mul] using he
  have hZrim (j i : Fin 2) {x : E2} (hx : x ∈ Z j i) (hn : ‖x‖ = 1) :
      ∃ e : Fin 2, F j 1 x = port (ep (i, e)) := by
    have hr := Real.sq_sqrt (by nlinarith [hmu j] : 0 ≤ (J2 x).1 ^ 2 + mu j)
    have hxx : (J2 x).1 ^ 2 = (1 - mu j) / 2 := by
      have hh := hJ2 x
      rw [hx.2, mul_pow, hs i, one_mul, hr, hn] at hh
      nlinarith
    have hax : Real.sqrt ((1 - mu j) / 2) = |(J2 x).1| := by
      rw [← hxx, Real.sqrt_sq_eq_abs]
    have hay : Real.sqrt ((J2 x).1 ^ 2 + mu j) = Real.sqrt ((1 + mu j) / 2) := by
      congr 1
      rw [hxx]
      ring
    have he : ∃ e : Fin 2, x = old j i e := by
      fin_cases i <;> rcases le_or_gt 0 (J2 x).1 with hp | hp
      · refine ⟨0, J2.injective ?_⟩
        apply Prod.ext <;> simp [old, sx, sy, sign, ep, finProdFinEquiv,
          hax, abs_of_nonneg hp, hx.2, hay,
          -Real.sqrt_div, -Real.sqrt_div']
      · refine ⟨1, J2.injective ?_⟩
        apply Prod.ext <;> simp [old, sx, sy, sign, ep, finProdFinEquiv,
          hax, abs_of_neg hp, hx.2, hay,
          -Real.sqrt_div, -Real.sqrt_div']
      · refine ⟨1, J2.injective ?_⟩
        apply Prod.ext <;> simp [old, sx, sy, sign, ep, finProdFinEquiv,
          hax, abs_of_nonneg hp, hx.2, hay,
          -Real.sqrt_div, -Real.sqrt_div']
      · refine ⟨0, J2.injective ?_⟩
        apply Prod.ext <;> simp [old, sx, sy, sign, ep, finProdFinEquiv,
          hax, abs_of_neg hp, hx.2, hay,
          -Real.sqrt_div, -Real.sqrt_div']
    obtain ⟨e, rfl⟩ := he
    exact ⟨e, (hold j i e).2⟩
  have hEnds (j i : Fin 2) : alpha j i 0 = kappa (port (ep (i, 0))) ∧
      alpha j i 1 = kappa (port (ep (i, 1))) := by
    constructor
    · simpa using hInitial j i 0 (by simpa using hnu)
    · simpa only [show (2 : ℝ) - 1 = 1 by norm_num, one_smul] using
        hTerminal j i 1 (by simpa using hnu)
  have hEtaK (j i : Fin 2) : Eta j i ⊆ K := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨F j 1 x, by simpa only [mem_closedBall, dist_zero_right, (hFn j x).1] using hx.1, rfl⟩
  have hBoundaryK (j i : Fin 2) : K ∩ (B j i).boundary = Eta j i := by
    ext y
    constructor
    · rintro ⟨hyK, hyB⟩
      rw [hBoundary j i] at hyB
      rcases hyB with ⟨t, ht, rfl⟩ | hy
      · have he : t = 0 ∨ t = 1 := by
          by_contra hh
          have hn := not_or.mp hh
          exact hProper j i ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hn.1),
            lt_of_le_of_ne ht.2 hn.2⟩, rfl⟩ hyK
        rcases he with rfl | rfl
        · rw [(hEnds j i).1]
          exact ⟨F j 1 (old j i 0), ⟨old j i 0, (hold j i 0).1, rfl⟩,
            congrArg kappa (hold j i 0).2⟩
        · rw [(hEnds j i).2]
          exact ⟨F j 1 (old j i 1), ⟨old j i 1, (hold j i 1).1, rfl⟩,
            congrArg kappa (hold j i 1).2⟩
      · exact hy
    · intro hy
      exact ⟨hEtaK j i hy, by rw [hBoundary j i]; exact Or.inr hy⟩
  have hrootNorm (j : Fin 2) (x : ℝ) :
      ‖J2.symm (x, Real.sqrt (mu j))‖ = Real.sqrt (x ^ 2 + mu j) := by
    have hm := Real.sq_sqrt (hmu j).le
    have hr := Real.sq_sqrt (by nlinarith [hmu j] : 0 ≤ x ^ 2 + mu j)
    nlinarith [hnorm x (Real.sqrt (mu j)), norm_nonneg (J2.symm (x, Real.sqrt (mu j))),
      Real.sqrt_nonneg (x ^ 2 + mu j)]
  have hShort (j i : Fin 2) : IsPreconnected (Short j i) := by
    apply Convex.isPreconnected
    intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_⟩
    · have hh := (convex_closedBall (0 : E2) 1)
        (by simpa only [mem_closedBall, dist_zero_right] using hx.1)
        (by simpa only [mem_closedBall, dist_zero_right] using hy.1) ha hb hab
      simpa only [mem_closedBall, dist_zero_right] using hh
    · have he : J2.symm ((J2 (a • x + b • y)).1, Real.sqrt (mu j)) =
          a • J2.symm ((J2 x).1, Real.sqrt (mu j)) + b • J2.symm ((J2 y).1, Real.sqrt (mu j)) := by
        apply J2.injective
        simp only [map_add, map_smul, J2.apply_symm_apply]
        apply Prod.ext
        · rfl
        · change Real.sqrt (mu j) = a * Real.sqrt (mu j) + b * Real.sqrt (mu j)
          rw [← add_mul, hab, one_mul]
      have hle := norm_add_le (a • J2.symm ((J2 x).1, Real.sqrt (mu j)))
        (b • J2.symm ((J2 y).1, Real.sqrt (mu j)))
      rw [← he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb, hrootNorm, hrootNorm, hrootNorm] at hle
      have hlt : a * Real.sqrt ((J2 x).1 ^ 2 + mu j) + b * Real.sqrt ((J2 y).1 ^ 2 + mu j) <
          a * (sign i * (J2 x).2) + b * (sign i * (J2 y).2) := by
        by_cases haz : a = 0
        · have hb1 : b = 1 := by linarith
          simpa [haz, hb1] using hy.2
        · exact add_lt_add_of_lt_of_le
            (mul_lt_mul_of_pos_left hx.2 (lt_of_le_of_ne ha (Ne.symm haz)))
            (mul_le_mul_of_nonneg_left hy.2.le hb)
      have hc : (J2 (a • x + b • y)).2 = a * (J2 x).2 + b * (J2 y).2 := by simp
      change Real.sqrt ((J2 (a • x + b • y)).1 ^ 2 + mu j) < sign i * (J2 (a • x + b • y)).2
      rw [hc]
      nlinarith
  have hLong0 (j i : Fin 2) : (0 : E2) ∈ Long j i := by
    simp only [Long, mem_ofPred_eq, norm_zero, map_zero, Prod.fst_zero, Prod.snd_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero]
    exact ⟨by norm_num, Real.sqrt_pos.mpr (hmu j)⟩
  have hLong (j i : Fin 2) : IsPreconnected (Long j i) := by
    have hstar : StarConvex ℝ (0 : E2) (Long j i) := by
      rw [starConvex_zero_iff]
      intro x hx t ht ht1
      refine ⟨?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
        nlinarith [norm_nonneg x, hx.1]
      · change sign i * (J2 (t • x)).2 < Real.sqrt ((J2 (t • x)).1 ^ 2 + mu j)
        rw [map_smul]
        change sign i * (t * (J2 x).2) < Real.sqrt ((t * (J2 x).1) ^ 2 + mu j)
        have hr : 0 < Real.sqrt ((t * (J2 x).1) ^ 2 + mu j) :=
          Real.sqrt_pos.mpr (by nlinarith [hmu j])
        by_cases hz : sign i * (J2 x).2 ≤ 0
        · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hz]
        · have hy : 0 < sign i * (J2 x).2 := lt_of_not_ge hz
          have hsq := Real.sq_sqrt (by nlinarith [hmu j] : 0 ≤ (J2 x).1 ^ 2 + mu j)
          have hsq' := Real.sq_sqrt (by nlinarith [hmu j] : 0 ≤ (t * (J2 x).1) ^ 2 + mu j)
          have hgap : (sign i * (J2 x).2) ^ 2 < (J2 x).1 ^ 2 + mu j := by nlinarith [hx.2]
          by_cases ht0 : t = 0
          · simpa [ht0] using Real.sqrt_pos.mpr (hmu j)
          · have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
            have hh := mul_lt_mul_of_pos_left hgap ht2
            have hm := mul_nonneg (by
              nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)] : 0 ≤ 1 - t ^ 2) (hmu j).le
            nlinarith [mul_nonneg ht hy.le]
    exact (hstar.isPathConnected (hLong0 j i)).isConnected.isPreconnected
  have hcompInj (j : Fin 2) {x y : E2} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
      (he : kappa (F j 1 x) = kappa (F j 1 y)) : x = y :=
    (F j 1).injective (kappa.injOn (hsrc (by
      change ‖F j 1 x‖ ≤ 2
      rw [(hFn j x).1]
      linarith)) (hsrc (by
        change ‖F j 1 y‖ ≤ 2
        rw [(hFn j y).1]
        linarith)) he)
  have hImagePre (j : Fin 2) {T : Set E2} (hT : IsPreconnected T)
      (hn : ∀ x ∈ T, ‖x‖ ≤ 1) : IsPreconnected (kappa '' ((F j 1) '' T)) := by
    apply (hT.image _ (F j 1).continuous.continuousOn).image
    apply kappa.continuousOn.mono
    rintro _ ⟨x, hx, rfl⟩
    exact hsrc (by rw [(hFn j x).1]; linarith [hn x hx])
  let top : Fin 2 → E2 := fun i => J2.symm (0, sign i)
  have htopN (i : Fin 2) : ‖top i‖ = 1 := by
    have hn := hnorm 0 (sign i)
    change ‖top i‖ ^ 2 = 0 ^ 2 + (sign i) ^ 2 at hn
    nlinarith [hs i, norm_nonneg (top i)]
  have htopF (j i : Fin 2) : F j 1 (top i) = top i := by
    have hf := (hFs j).2.2.1 1 (top i)
    simpa [top] using hf
  have htopS (j i : Fin 2) : top i ∈ Short j i := by
    refine ⟨(htopN i).le, ?_⟩
    simp only [top, J2.apply_symm_apply, zero_pow (by decide : 2 ≠ 0), zero_add]
    have hm := Real.sq_sqrt (hmu j).le
    nlinarith [hs i, hmuSmall j, Real.sqrt_nonneg (mu j)]
  have hFzero (j : Fin 2) : F j 1 (0 : E2) = 0 :=
    norm_eq_zero.mp (by simpa only [norm_zero] using (hFn j 0).1)
  have hFill (j i : Fin 2) :
      kappa '' ((F j 1) '' Short j i) ⊆ (B j i).inside ∧
      kappa '' ((F j 1) '' Long j i) ⊆ (B j i).closedRegionᶜ := by
    have hcover : K \ Eta j i =
        (kappa '' ((F j 1) '' Short j i)) ∪ (kappa '' ((F j 1) '' Long j i)) := by
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hn⟩
        let x := (F j 1).symm z
        have hx : ‖x‖ ≤ 1 := by
          simpa only [x, (hFn j z).2, mem_closedBall, dist_zero_right] using hz
        have he : (J2 x).2 ≠ sign i * Real.sqrt ((J2 x).1 ^ 2 + mu j) := by
          intro he
          exact hn ⟨F j 1 x, ⟨x, ⟨hx, he⟩, rfl⟩, by simp [x]⟩
        have hne : Real.sqrt ((J2 x).1 ^ 2 + mu j) ≠ sign i * (J2 x).2 := by
          intro hh
          apply he
          have hm := congrArg (fun r : ℝ => sign i * r) hh
          rw [← mul_assoc, ← pow_two, hs i, one_mul] at hm
          exact hm.symm
        rcases lt_or_gt_of_ne hne with hh | hh
        · exact Or.inl ⟨F j 1 x, ⟨x, ⟨hx, hh⟩, rfl⟩, by simp [x]⟩
        · exact Or.inr ⟨F j 1 x, ⟨x, ⟨hx, hh⟩, rfl⟩, by simp [x]⟩
      · rintro (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
        all_goals
          refine ⟨⟨F j 1 x, by
            simpa only [mem_closedBall, dist_zero_right, (hFn j x).1] using hx.1, rfl⟩, ?_⟩
          rintro ⟨_, ⟨z, hz, rfl⟩, he⟩
          have hzx := hcompInj j hz.1 hx.1 he
          subst z
          have hr : sign i * (J2 x).2 = Real.sqrt ((J2 x).1 ^ 2 + mu j) := by
            rw [hz.2, ← mul_assoc, ← pow_two, hs i, one_mul]
          nlinarith [hx.2, hr]
    let o : Fin 2 := Equiv.swap (0 : Fin 2) 1 i
    let z : E2 := Real.sqrt (mu j) • top o
    have ho : sign o = -sign i := by fin_cases i <;> norm_num [o, sign, Equiv.swap_apply_def]
    have hzn : ‖z‖ = Real.sqrt (mu j) := by
      simp only [z, norm_smul, htopN, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hzm : ‖z‖ < 1 := by
      rw [hzn]
      nlinarith [Real.sq_sqrt (hmu j).le, Real.sqrt_nonneg (mu j), hmuSmall j]
    have hzZ : z ∈ Z j o := by
      refine ⟨hzm.le, ?_⟩
      simp [z, top, mul_comm]
    have hzL : z ∈ Long j i := by
      refine ⟨hzm.le, ?_⟩
      simp only [z, top, map_smul, J2.apply_symm_apply, Prod.smul_mk, smul_eq_mul]
      simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
      rw [ho]
      rw [show sign i * (Real.sqrt (mu j) * -sign i) = -(sign i) ^ 2 * Real.sqrt (mu j) by ring,
        hs i]
      nlinarith [Real.sqrt_pos.mpr (hmu j)]
    have hdis : Disjoint (B j i).closedRegion (B j o).closedRegion := by
      fin_cases i
      · simpa [o] using hCase j
      · simpa [o] using (hCase j).symm
    have hout : kappa (F j 1 z) ∉ (B j i).closedRegion := by
      intro hy
      apply disjoint_left.mp hdis hy
      rw [← (B j o).inside_union_boundary, hBoundary j o]
      exact Or.inr (Or.inr ⟨F j 1 z, ⟨z, hzZ, rfl⟩, rfl⟩)
    let z' : E2 := Real.sqrt (mu j) • top i
    have hz'n : ‖z'‖ < 1 := by
      have hn : ‖z'‖ = Real.sqrt (mu j) := by
        simp only [z', norm_smul, htopN, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [hn]
      nlinarith [Real.sq_sqrt (hmu j).le, Real.sqrt_nonneg (mu j), hmuSmall j]
    have hz'Z : z' ∈ Z j i := by refine ⟨hz'n.le, ?_⟩; simp [z', top, mul_comm]
    have hOpen : IsOpen (kappa '' ball (0 : E2) 1) :=
      kappa.isOpen_image_of_subset_source isOpen_ball
      (fun x hx => hsrc (by have hn := mem_ball_zero_iff.mp hx; linarith))
    have hz'K : kappa (F j 1 z') ∈ interior K :=
      (interior_maximal (image_mono ball_subset_closedBall) hOpen)
        ⟨F j 1 z', by simpa only [mem_ball, dist_zero_right, (hFn j z').1] using hz'n, rfl⟩
    exact saddle_crosscut_cells_inside_outside (B j i) K
      (kappa '' ((F j 1) '' Short j i)) (kappa '' ((F j 1) '' Long j i)) (Eta j i)
      hcover (hBoundaryK j i) (hImagePre j (hShort j i) (fun _ hx => hx.1))
      (hImagePre j (hLong j i) (fun _ hx => hx.1))
      ⟨kappa (F j 1 z), ⟨F j 1 z, ⟨z, hzL, rfl⟩, rfl⟩, hout⟩
      ⟨kappa (F j 1 z'), ⟨F j 1 z', ⟨z', hz'Z, rfl⟩, rfl⟩, hz'K⟩
  let M : Set E2 := ⋃ j : Fin 2, ⋃ i : Fin 2, alpha j i '' Icc (nu / 2) (1 - nu / 2)
  have hMc : IsCompact M := isCompact_iUnion (fun j => isCompact_iUnion (fun i =>
    isCompact_Icc.image_of_continuousOn ((hAlpha j i).continuousOn.mono (by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩))))
  have hKM : K ⊆ Mᶜ := by
    intro y hy hM
    obtain ⟨j, hM⟩ := mem_iUnion.mp hM
    obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hM
    exact hProper j i ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩ hy
  obtain ⟨d, hd, hdsub⟩ := (isCompact_closedBall (0 : E2) 1).exists_thickening_subset_open
    (kappa.isOpen_inter_preimage hMc.isClosed.isOpen_compl) (by
      intro x hx
      exact ⟨hsrc (by have hn := mem_closedBall_zero_iff.mp hx; linarith), hKM ⟨x, hx, rfl⟩⟩)
  rw [thickening_closedBall hd zero_le_one] at hdsub
  let h : ℝ := min (nu / 256) (min (1 / 2048) (d / 128))
  have hh : 0 < h := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hnuB : h < nu / 128 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsm : h < 1 / 1024 :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hdB : 32 * h < d := by
    have he : h ≤ d / 128 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hAnn {x : E2} (hx : ‖x‖ ≤ 1 + 32 * h) : x ∈ kappa.source ∧ kappa x ∉ M :=
    hdsub (by simpa only [mem_ball, dist_zero_right] using (show ‖x‖ < d + 1 by linarith))
  have hRayN (i e : Fin 2) (r : ℝ) (hr : 0 ≤ r) : ‖r • port (ep (i, e))‖ = r := by
    simp only [norm_smul, hportN, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]
  have hRayA (j i e : Fin 2) (r : ℝ) (hr : r ∈ Icc 1 (1 + 32 * h)) :
      kappa (r • port (ep (i, e))) ∈ alpha j i '' Icc (0 : ℝ) 1 := by
    fin_cases e
    · refine ⟨r - 1, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
      have he := hInitial j i (r - 1) (by rw [abs_of_nonneg (by linarith [hr.1])]; linarith [hr.2])
      change alpha j i (r - 1) = kappa (r • port (ep (i, 0)))
      simpa only [add_sub_cancel] using he
    · refine ⟨2 - r, ⟨by linarith [hr.2], by linarith [hr.1]⟩, ?_⟩
      have he := hTerminal j i (2 - r) (by rw [abs_of_nonpos (by linarith [hr.1])]; linarith [hr.2])
      change alpha j i (2 - r) = kappa (r • port (ep (i, 1)))
      simpa only [sub_sub_cancel] using he
  have hExact (j i : Fin 2) :
      (alpha j i '' Icc (0 : ℝ) 1) ∩ (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
        kappa '' (((fun r : ℝ => r • port (ep (i, 0))) '' Icc 1 (1 + 32 * h)) ∪
          ((fun r : ℝ => r • port (ep (i, 1))) '' Icc 1 (1 + 32 * h))) := by
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, ⟨x, hx, heq⟩⟩
      have htm : t ∉ Icc (nu / 2) (1 - nu / 2) := by
        intro hm
        apply (hAnn hx.2).2
        rw [heq]
        exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨i, ⟨t, hm, rfl⟩⟩⟩
      rcases lt_or_ge t (nu / 2) with htl | htl
      · have he := hInitial j i t (by rw [abs_of_nonneg ht.1]; linarith)
        have hp : (1 + t) • port (ep (i, 0)) ∈ kappa.source :=
          hsrc (by rw [hRayN i 0 (1 + t) (by linarith [ht.1])]; linarith)
        have hxp := kappa.injOn (hAnn hx.2).1 hp (heq.trans he)
        have hn : 1 + t ∈ Icc 1 (1 + 32 * h) := by
          change 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h at hx
          rw [hxp, hRayN i 0 (1 + t) (by linarith [ht.1])] at hx
          exact hx
        exact ⟨(1 + t) • port (ep (i, 0)), Or.inl ⟨1 + t, hn, rfl⟩, he.symm⟩
      · have htr : 1 - nu / 2 < t := lt_of_not_ge (fun ht' => htm ⟨htl, ht'⟩)
        have he := hTerminal j i t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith)
        have hp : (2 - t) • port (ep (i, 1)) ∈ kappa.source :=
          hsrc (by rw [hRayN i 1 (2 - t) (by linarith [ht.2])]; linarith)
        have hxp := kappa.injOn (hAnn hx.2).1 hp (heq.trans he)
        have hn : 2 - t ∈ Icc 1 (1 + 32 * h) := by
          change 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h at hx
          rw [hxp, hRayN i 1 (2 - t) (by linarith [ht.2])] at hx
          exact hx
        exact ⟨(2 - t) • port (ep (i, 1)), Or.inr ⟨2 - t, hn, rfl⟩, he.symm⟩
    · rintro ⟨x, (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩), rfl⟩
      · exact ⟨hRayA j i 0 r hr, ⟨_, by
          simpa only [mem_ofPred_eq, mem_Icc, hRayN i 0 r (by linarith [hr.1])] using hr, rfl⟩⟩
      · exact ⟨hRayA j i 1 r hr, ⟨_, by
          simpa only [mem_ofPred_eq, mem_Icc, hRayN i 1 r (by linarith [hr.1])] using hr, rfl⟩⟩
  let Sector : Fin 2 → Set E2 := fun i =>
    {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧ |(J2 x).1| < sign i * (J2 x).2}
  have hSectorPre (i : Fin 2) : IsPreconnected (Sector i) := by
    let f : ℝ × ℝ → E2 := fun p => (p.1 / Real.sqrt (p.2 ^ 2 + 1)) • J2.symm (p.2, sign i)
    have hn (a : ℝ) : ‖J2.symm (a, sign i)‖ = Real.sqrt (a ^ 2 + 1) := by
      have hr := Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + 1)
      nlinarith [hnorm a (sign i), hs i, norm_nonneg (J2.symm (a, sign i)),
        Real.sqrt_nonneg (a ^ 2 + 1)]
    have hfc : Continuous f := by
      change Continuous (fun p : ℝ × ℝ =>
        (p.1 / Real.sqrt (p.2 ^ 2 + 1)) • J2.symm (p.2, sign i))
      apply Continuous.smul (f := fun p : ℝ × ℝ => p.1 / Real.sqrt (p.2 ^ 2 + 1))
        (g := fun p : ℝ × ℝ => J2.symm (p.2, sign i))
      · exact continuous_fst.div
          (Real.continuous_sqrt.comp ((continuous_snd.pow 2).add continuous_const))
          (fun p => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
      · exact J2.symm.continuous.comp (continuous_snd.prodMk continuous_const)
    have hrange : f '' (Icc 1 (1 + 32 * h) ×ˢ Ioo (-1 : ℝ) 1) = Sector i := by
      ext x
      constructor
      · rintro ⟨⟨r, a⟩, ⟨hr, ha⟩, rfl⟩
        have hd : 0 < Real.sqrt (a ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
        have hr0 : 0 < r := by linarith [hr.1]
        have hnf : ‖f (r, a)‖ = r := by
          simp only [f, norm_smul, hn, Real.norm_eq_abs, abs_of_pos (div_pos hr0 hd)]
          exact div_mul_cancel₀ r hd.ne'
        refine ⟨by simpa only [hnf] using hr.1, by simpa only [hnf] using hr.2, ?_⟩
        simp only [f, map_smul, J2.apply_symm_apply, Prod.smul_mk, smul_eq_mul]
        rw [abs_mul, abs_of_pos (div_pos hr0 hd)]
        have ha' : |a| < 1 := abs_lt.mpr ha
        have hh := mul_lt_mul_of_pos_left ha' (div_pos hr0 hd)
        have he : sign i * (r / Real.sqrt (a ^ 2 + 1) * sign i) = r / Real.sqrt (a ^ 2 + 1) := by
          calc
            _ = (sign i) ^ 2 * (r / Real.sqrt (a ^ 2 + 1)) := by ring
            _ = _ := by rw [hs i, one_mul]
        rw [he]
        simpa only [mul_one] using hh
      · intro hx
        let a : ℝ := (J2 x).1 / (sign i * (J2 x).2)
        have hy : 0 < sign i * (J2 x).2 := (abs_nonneg _).trans_lt hx.2.2
        have ha : |a| < 1 := by
          dsimp only [a]
          rw [abs_div, abs_of_pos hy, div_lt_one hy]
          exact hx.2.2
        have hd : 0 < Real.sqrt (a ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
        have hsx : Real.sqrt (a ^ 2 + 1) * (sign i * (J2 x).2) = ‖x‖ := by
          have he : (a ^ 2 + 1) * (sign i * (J2 x).2) ^ 2 = ‖x‖ ^ 2 := by
            calc
              _ = (J2 x).1 ^ 2 + (sign i * (J2 x).2) ^ 2 := by
                dsimp only [a]
                rw [add_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hy.ne'), one_mul]
              _ = ‖x‖ ^ 2 := by rw [mul_pow, hs i, one_mul]; exact hJ2 x
          have he' : (Real.sqrt (a ^ 2 + 1) * (sign i * (J2 x).2)) ^ 2 = ‖x‖ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + 1), he]
          nlinarith [he', mul_pos hd hy, norm_nonneg x]
        refine ⟨(‖x‖, a), ⟨⟨hx.1, hx.2.1⟩, abs_lt.mp ha⟩, J2.injective ?_⟩
        have he : ‖x‖ / Real.sqrt (a ^ 2 + 1) = sign i * (J2 x).2 :=
          (div_eq_iff hd.ne').mpr (by linarith [hsx])
        simp only [f, map_smul, J2.apply_symm_apply, Prod.smul_mk, smul_eq_mul, he]
        apply Prod.ext
        · dsimp only [a]
          exact mul_div_cancel₀ _ hy.ne'
        · calc
            _ = (sign i) ^ 2 * (J2 x).2 := by ring
            _ = _ := by rw [hs i, one_mul]
    rw [← hrange]
    exact (isPreconnected_Icc.prod isPreconnected_Ioo).image _ hfc.continuousOn
  have hSectorInside (j i : Fin 2) : kappa '' Sector i ⊆ (B j i).inside := by
    have hpre := (hSectorPre i).image kappa (kappa.continuousOn.mono (fun _ hx => (hAnn hx.2.1).1))
    have hdis : Disjoint (kappa '' Sector i) (B j i).boundary := by
      apply disjoint_left.mpr
      rintro _ ⟨x, hx, rfl⟩ hy
      rw [hBoundary j i] at hy
      rcases hy with hy | ⟨_, ⟨z, hz, rfl⟩, he⟩
      · have he : kappa x ∈ (alpha j i '' Icc (0 : ℝ) 1) ∩
            (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) := ⟨hy, ⟨x, ⟨hx.1, hx.2.1⟩, rfl⟩⟩
        rw [hExact j i] at he
        rcases he with ⟨_, ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩, he⟩
        · have he' := kappa.injOn (hAnn (by rw [hRayN i 0 r (by linarith [hr.1])]; exact hr.2)).1
            (hAnn hx.2.1).1 he
          have hc := hportCone i 0 r (by linarith [hr.1])
          change r • port (ep (i, 0)) = x at he'
          rw [he'] at hc
          exact (ne_of_lt hx.2.2) hc
        · have he' := kappa.injOn (hAnn (by rw [hRayN i 1 r (by linarith [hr.1])]; exact hr.2)).1
            (hAnn hx.2.1).1 he
          have hc := hportCone i 1 r (by linarith [hr.1])
          change r • port (ep (i, 1)) = x at he'
          rw [he'] at hc
          exact (ne_of_lt hx.2.2) hc
      · have he' := kappa.injOn (hsrc (by rw [(hFn j z).1]; linarith [hz.1])) (hAnn hx.2.1).1 he
        have hn : ‖z‖ = 1 := by
          rw [← (hFn j z).1, he']
          exact le_antisymm (by rw [← he', (hFn j z).1]; exact hz.1) hx.1
        obtain ⟨e, hp⟩ := hZrim j i hz hn
        have hc := hportCone i e 1 zero_le_one
        simp only [one_smul, ← hp, he'] at hc
        exact (ne_of_lt hx.2.2) hc
    have htopSector : top i ∈ Sector i := by
      refine ⟨by rw [htopN], by rw [htopN]; linarith, ?_⟩
      simp only [top, J2.apply_symm_apply, abs_zero]
      nlinarith [hs i]
    have htopInside : kappa (top i) ∈ (B j i).inside := by
      apply (hFill j i).1
      exact ⟨F j 1 (top i), ⟨top i, htopS j i, rfl⟩, congrArg kappa (htopF j i)⟩
    rcases (B j i).preconnected_subset_inside_or_outside hpre hdis with hi | ho
    · exact hi
    · exact False.elim (ho ⟨top i, htopSector, rfl⟩ (by
        rw [← (B j i).inside_union_boundary]; exact Or.inl htopInside))
  refine ⟨h, hh, hnuB, hsm, ?_, hExact, hSectorInside, ?_⟩
  · intro j i
    refine ⟨(hFill j i).1, (hFill j i).2, ?_⟩
    exact (hFill j i).2 ⟨F j 1 0, ⟨0, hLong0 j i, rfl⟩, congrArg kappa (hFzero j)⟩
  · intro j i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    by_cases he : |(J2 x).1| < sign i * (J2 x).2
    · rw [← (B j i).inside_union_boundary]
      exact Or.inl (hSectorInside j i ⟨x, ⟨hx.1, hx.2.1, he⟩, rfl⟩)
    · have heq : |(J2 x).1| = sign i * (J2 x).2 := le_antisymm hx.2.2 (le_of_not_gt he)
      have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hsy2 : (sign i * (J2 x).2) ^ 2 = (J2 x).2 ^ 2 := by
        rw [mul_pow, hs i, one_mul]
      have hypos : 0 < sign i * (J2 x).2 := by
        have hn := hJ2 x
        nlinarith [sq_abs ((J2 x).1), hsy2, hx.1, abs_nonneg ((J2 x).1)]
      have hyval : sign i * (J2 x).2 = ‖x‖ / Real.sqrt 2 := by
        apply (eq_div_iff h2p.ne').mpr
        have hp : (sign i * (J2 x).2 * Real.sqrt 2) ^ 2 = ‖x‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          nlinarith [hJ2 x, sq_abs ((J2 x).1), hsy2]
        nlinarith [hp, mul_pos hypos h2p, norm_nonneg x]
      have hray : ∃ e : Fin 2, x = ‖x‖ • port (ep (i, e)) := by
        have hxval : |(J2 x).1| = ‖x‖ / Real.sqrt 2 := heq.trans hyval
        simp only [div_eq_mul_inv] at hxval hyval
        fin_cases i <;> norm_num [sign] at hyval <;>
          rcases le_or_gt 0 (J2 x).1 with hxp | hxp
        · refine ⟨0, J2.injective ?_⟩
          rw [abs_of_nonneg hxp] at hxval
          apply Prod.ext <;> simp [port, ep, finProdFinEquiv, sx, sy, map_smul, div_eq_mul_inv] <;>
            nlinarith only [hxval, hyval]
        · refine ⟨1, J2.injective ?_⟩
          rw [abs_of_neg hxp] at hxval
          apply Prod.ext <;> simp [port, ep, finProdFinEquiv, sx, sy, map_smul, div_eq_mul_inv] <;>
            nlinarith only [hxval, hyval]
        · refine ⟨1, J2.injective ?_⟩
          rw [abs_of_nonneg hxp] at hxval
          apply Prod.ext <;> simp [port, ep, finProdFinEquiv, sx, sy, map_smul, div_eq_mul_inv] <;>
            nlinarith only [hxval, hyval]
        · refine ⟨0, J2.injective ?_⟩
          rw [abs_of_neg hxp] at hxval
          apply Prod.ext <;> simp [port, ep, finProdFinEquiv, sx, sy, map_smul, div_eq_mul_inv] <;>
            nlinarith only [hxval, hyval]
      obtain ⟨e, he⟩ := hray
      rw [← (B j i).inside_union_boundary, hBoundary j i]
      have hh := hRayA j i e ‖x‖ ⟨hx.1, hx.2.1⟩
      rw [← he] at hh
      exact Or.inr (Or.inl hh)

end PoincareConjecture.M25.Topology3D
