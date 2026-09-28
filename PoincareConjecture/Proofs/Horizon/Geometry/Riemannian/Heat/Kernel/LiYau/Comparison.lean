import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.NoncompactMaximum
import Mathlib.Analysis.Calculus.Deriv.Mul



set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Parabolic

private lemma quadratic_bound_nonpos {N C k T s Y : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) (hk : 0 ≤ k) (hs : 0 ≤ s) (hsT : s ≤ T)
    (hY : 4 * N * (1 + (C + k) * T) < Y) :
    (1 + C * s) * Y - Y ^ 2 / (2 * N) + 2 * N * k ^ 2 * s ^ 2 ≤ 0 := by
  have hT := hs.trans hsT
  have hY0 : 0 < Y := lt_of_le_of_lt (by positivity) hY
  have hc : C * s ≤ C * T := mul_le_mul_of_nonneg_left hsT hC
  have hk' : k * s ≤ k * T := mul_le_mul_of_nonneg_left hsT hk
  have hYs : 4 * N * (1 + C * s + k * s) < Y := by nlinarith
  have hYs' := mul_le_mul_of_nonneg_right hYs.le hY0.le
  have hYk : 4 * N * k * s ≤ Y := by nlinarith [mul_nonneg hC hs]
  have hYk' := mul_le_mul_of_nonneg_right hYk (mul_nonneg hk hs)
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * N by positivity)).mp
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hk hs) hY0.le]



theorem weighted_quadratic_bound_on_interval
    {X : Type*} [TopologicalSpace X] {q qt : X → ℝ → ℝ} {η : X → ℝ}
    {N C k a b : ℝ} (hN : 0 < N) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hab : a ≤ b) (hηc : HasCompactSupport η) (hη : ∀ x, η x ∈ Icc 0 1)
    (hcont : ContinuousOn (fun p : X × ℝ => η p.1 * q p.1 p.2) (univ ×ˢ Icc a b))
    (hderiv : ∀ x t, t ∈ Ioc a b → HasDerivAt (q x) (qt x t) t)
    (hmax : ∀ x t, t ∈ Ioc a b → 0 < η x * q x t →
      (∀ y, η y * q y t ≤ η x * q x t) →
      η x ^ 2 * qt x t ≤ C * (η x * q x t) -
        (η x * q x t) ^ 2 / (2 * N) + 2 * N * k ^ 2) :
    ∀ x t, t ∈ Icc a b →
      (t - a) * η x * q x t ≤ 4 * N * (1 + (C + k) * (b - a)) := by
  let L := 4 * N * (1 + (C + k) * (b - a))
  have hL : 0 < L := by dsimp [L]; positivity
  let F := fun x t => (t - a) * (η x * q x t) - L
  let F' := fun x t => η x * q x t + (t - a) * η x * qt x t
  have hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b) :=
    ((continuous_snd.sub continuous_const).continuousOn.mul hcont).sub continuousOn_const
  have hd (x : X) (t : ℝ) (ht : t ∈ Ioc a b) :
      HasDerivWithinAt (F x) (F' x t) (Icc a b) t := by
    have h := (((hasDerivAt_id t).sub_const a).mul
      ((hderiv x t ht).const_mul (η x))).sub_const L
    simpa [F, F', Pi.mul_def, mul_assoc] using h.hasDerivWithinAt (s := Icc a b)
  have hbound := nonpos_of_deriv_le_mul_at_max_of_nonpos_outside_compact
    hηc hF hd (c := 0) (fun x t ht hpos hsp => ?_)
    (fun x => by dsimp [F]; simpa using hL.le)
    (fun x hx t _ => by simp [F, image_eq_zero_of_notMem_tsupport hx, hL.le])
  · intro x t ht
    have h := hbound x t ht
    dsimp [F] at h
    dsimp [L] at h ⊢
    nlinarith
  · have hs : 0 < t - a := sub_pos.mpr ht.1
    have hQ : 0 < η x * q x t := by dsimp [F] at hpos; nlinarith
    have hηpos : 0 < η x := lt_of_le_of_ne (hη x).1 (by
      intro he; rw [← he, zero_mul] at hQ; exact (lt_irrefl 0) hQ)
    have hm := hmax x t ht hQ (fun y => by
      have h := hsp y
      dsimp [F] at h
      nlinarith)
    have hmult := mul_le_mul_of_nonneg_left hm (sq_nonneg (t - a))
    have hηY : η x * ((t - a) * (η x * q x t)) ≤ (t - a) * (η x * q x t) :=
      mul_le_of_le_one_left (mul_nonneg hs.le hQ.le) (hη x).2
    have hquad := quadratic_bound_nonpos hN hC hk hs.le
      (show t - a ≤ b - a by linarith [ht.2])
      (show 4 * N * (1 + (C + k) * (b - a)) < (t - a) * (η x * q x t) by
        exact sub_pos.mp hpos)
    have hid : ((t - a) * (η x * q x t)) ^ 2 / (2 * N) =
        (t - a) ^ 2 * ((η x * q x t) ^ 2 / (2 * N)) := by ring
    rw [hid] at hquad
    change F' x t ≤ 0 * F x t
    dsimp [F', F]
    have hweight : 0 < (t - a) * η x := mul_pos hs hηpos
    nlinarith



theorem weighted_quadratic_bound
    {X : Type*} [TopologicalSpace X] {q qt : X → ℝ → ℝ} {η : X → ℝ}
    {N C k : ℝ} (hN : 0 < N) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hηc : HasCompactSupport η) (hη : ∀ x, η x ∈ Icc 0 1)
    (hcont : ContinuousOn (fun p : X × ℝ => η p.1 * q p.1 p.2) (univ ×ˢ Ioi 0))
    (hderiv : ∀ x t, 0 < t → HasDerivAt (q x) (qt x t) t)
    (hmax : ∀ x t, 0 < t → 0 < η x * q x t →
      (∀ y, η y * q y t ≤ η x * q x t) →
      η x ^ 2 * qt x t ≤ C * (η x * q x t) -
        (η x * q x t) ^ 2 / (2 * N) + 2 * N * k ^ 2) :
    ∀ x t, 0 < t → t * η x * q x t ≤ 4 * N * (1 + (C + k) * t) := by
  intro x t ht
  have hev : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (t - a) * η x * q x t ≤ 4 * N * (1 + (C + k) * t) := by
    filter_upwards [Ioo_mem_nhdsGT ht] with a ha
    have hb := weighted_quadratic_bound_on_interval hN hC hk ha.2.le hηc hη
      (hcont.mono (prod_mono Subset.rfl (fun s hs => ha.1.trans_le hs.1)))
      (fun y s hs => hderiv y s (ha.1.trans hs.1))
      (fun y s hs => hmax y s (ha.1.trans hs.1)) x t ⟨ha.2.le, le_rfl⟩
    apply hb.trans
    have h := mul_le_mul_of_nonneg_left (show t - a ≤ t by linarith [ha.1])
      (show 0 ≤ C + k by positivity)
    nlinarith
  have hc : ContinuousAt (fun a : ℝ => (t - a) * η x * q x t) 0 := by fun_prop
  exact le_of_tendsto (by simpa using hc.tendsto.mono_left nhdsWithin_le_nhds) hev

end Poincare.Parabolic
