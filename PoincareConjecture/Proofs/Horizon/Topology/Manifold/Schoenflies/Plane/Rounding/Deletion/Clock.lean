import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.RoundedVertexPath
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicFiber











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Topology ContDiff Manifold

namespace Poincare.Manifold.Schoenflies.Plane


noncomputable def deletionClockVertex (N : ℕ) (j : ℤ) : ℝ :=
  (j : ℝ) - ((j / (N : ℤ) : ℤ) + ((j + 1) / (N : ℤ) : ℤ) : ℝ) / 2

theorem deletionClockVertex_add_period {N : ℕ} (hN : 0 < N) (j : ℤ) :
    deletionClockVertex N (j + N) = deletionClockVertex N j + (N : ℝ) - 1 := by
  have hn : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hq (k : ℤ) : (k + N) / (N : ℤ) = k / (N : ℤ) + 1 := by
    rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hn]
  simp only [deletionClockVertex, show j + (N : ℤ) + 1 = (j + 1) + N by omega,
    hq, Int.cast_add, Int.cast_natCast, Int.cast_one]
  ring


theorem deletionClockVertex_step_bounds {N : ℕ} (hN : 2 ≤ N) (j : ℤ) :
    1 / 2 ≤ deletionClockVertex N (j + 1) - deletionClockVertex N j ∧
      deletionClockVertex N (j + 1) - deletionClockVertex N j ≤ 1 := by
  have hn : (0 : ℤ) < N := by omega
  have hlo : j / (N : ℤ) ≤ (j + 2) / (N : ℤ) := Int.ediv_le_ediv hn (by omega)
  have hhi : (j + 2) / (N : ℤ) ≤ j / (N : ℤ) + 1 := by
    calc
      (j + 2) / (N : ℤ) ≤ (j + N) / (N : ℤ) := Int.ediv_le_ediv hn (by omega)
      _ = j / (N : ℤ) + 1 := by
        rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hn.ne']
  have hlo' : ((j / (N : ℤ) : ℤ) : ℝ) ≤ ((j + 2) / (N : ℤ) : ℤ) :=
    by exact_mod_cast hlo
  have hhi' : (((j + 2) / (N : ℤ) : ℤ) : ℝ) ≤ (j / (N : ℤ) : ℤ) + 1 :=
    by exact_mod_cast hhi
  simp only [deletionClockVertex, show j + 1 + 1 = j + 2 by omega,
    Int.cast_add, Int.cast_one]
  constructor <;> linarith


theorem roundedVertexPath_add_period (ρ : ℝ → ℝ) (P : ℤ → ℝ) (N : ℤ) (T : ℝ)
    (hP : ∀ j, P (j + N) = P j + T) (t : ℝ) :
    roundedVertexPath ρ P (t + N) = roundedVertexPath ρ P t + T := by
  have hfloor : ⌊t + (N : ℝ) + 1 / 2⌋ = ⌊t + 1 / 2⌋ + N := by
    rw [show t + (N : ℝ) + 1 / 2 = (t + 1 / 2) + N by ring,
      Int.floor_add_intCast]
  simp only [roundedVertexPath, hfloor, Int.cast_add]
  rw [show ⌊t + 1 / 2⌋ + N - 1 = (⌊t + 1 / 2⌋ - 1) + N by omega,
    show ⌊t + 1 / 2⌋ + N + 1 = (⌊t + 1 / 2⌋ + 1) + N by omega]
  rw [show t + (N : ℝ) - (↑⌊t + 1 / 2⌋ + N) = t - ↑⌊t + 1 / 2⌋ by ring]
  simp only [hP, roundedCorner, smul_eq_mul]
  ring


theorem deriv_roundedVertexPath_mem_Icc {ρ : ℝ → ℝ} (P : ℤ → ℝ) {δ a b : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1)
    (hP : ∀ j, P (j + 1) - P j ∈ Icc a b) (t : ℝ) :
    deriv (roundedVertexPath ρ P) t ∈ Icc a b := by
  let i : ℤ := ⌊t + 1 / 2⌋
  have hilo : (i : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hihi : t + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
    constructor <;> linarith
  have hlocal : roundedVertexPath ρ P =ᶠ[𝓝 t]
      fun s => roundedCorner ρ (P i) (P i - P (i - 1)) (P (i + 1) - P i) (s - i) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact roundedVertexPath_eq_local P hδ hδhalf htail hbound i hs
  have hd := (hasDerivAt_roundedCorner (P i) (P i - P (i - 1))
    (P (i + 1) - P i) (hρ (t - i))).scomp t ((hasDerivAt_id t).sub_const (i : ℝ))
  simp only [Function.comp_def, one_smul, id_eq] at hd
  rw [(hd.congr_of_eventuallyEq hlocal).deriv]
  have hleft : P i - P (i - 1) ∈ Icc a b := by
    simpa only [sub_add_cancel] using hP (i - 1)
  have hright := hP i
  have hl : 0 ≤ (1 - deriv ρ (t - i)) / 2 := by
    linarith [(abs_le.mp (hder (t - i))).2]
  have hr : 0 ≤ (1 + deriv ρ (t - i)) / 2 := by
    linarith [(abs_le.mp (hder (t - i))).1]
  simp only [smul_eq_mul, mem_Icc]
  constructor
  · nlinarith [mul_nonneg hl (sub_nonneg.mpr hleft.1),
      mul_nonneg hr (sub_nonneg.mpr hright.1)]
  · nlinarith [mul_nonneg hl (sub_nonneg.mpr hleft.2),
      mul_nonneg hr (sub_nonneg.mpr hright.2)]


noncomputable def deletionClock (ρ : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
  roundedVertexPath ρ (deletionClockVertex N)

theorem deletionClock_add_period (ρ : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    deletionClock ρ N (t + N) = deletionClock ρ N t + (N : ℝ) - 1 := by
  simpa only [deletionClock, Int.cast_natCast, add_sub_assoc] using
    roundedVertexPath_add_period ρ (deletionClockVertex N) (N : ℤ) ((N : ℝ) - 1)
      (fun j => by simpa only [add_sub_assoc] using deletionClockVertex_add_period hN j) t

theorem contDiff_deletionClock {ρ : ℝ → ℝ} {δ : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (deletionClock ρ N) := by
  have hP (j : ℤ) : ContDiff ℝ ∞ (fun _ : ℝ => deletionClockVertex N j) := contDiff_const
  have hc : ContDiff ℝ ∞ (fun x : ℝ × ℝ => roundedVertexPath ρ (deletionClockVertex N) x.2) :=
    contDiff_roundedVertexPath (E := ℝ) (V := ℝ) (P := fun _ => deletionClockVertex N)
      hδ hδhalf htail hbound hρ hP
  have hcomp := hc.comp (show ContDiff ℝ ∞ (fun t : ℝ => ((0 : ℝ), t)) from
    contDiff_const.prodMk contDiff_id)
  convert hcomp using 1
  rfl

theorem deriv_deletionClock_mem_Icc {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1) (t : ℝ) :
    deriv (deletionClock ρ N) t ∈ Icc (1 / 2) 1 :=
  deriv_roundedVertexPath_mem_Icc (deletionClockVertex N) hδ hδhalf htail hbound hρ hder
    (deletionClockVertex_step_bounds hN) t

theorem strictMono_deletionClock {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1) :
    StrictMono (deletionClock ρ N) := by
  apply strictMono_of_deriv_pos
  intro t
  linarith [(deriv_deletionClock_mem_Icc hN hδ hδhalf htail hbound hρ hder t).1]


theorem surjective_of_add_periods {f : ℝ → ℝ} {T U : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hf : Continuous f) (hper : ∀ t, f (t + T) = f t + U) : Surjective f := by
  have hs : Surjective (fun t => (T / U) * f t) :=
    surjective_of_add_period hT (continuous_const.mul hf) (fun t => by
      rw [hper]
      field_simp)
  intro y
  obtain ⟨x, hx⟩ := hs ((T / U) * y)
  exact ⟨x, mul_left_cancel₀ (div_ne_zero hT.ne' hU.ne') hx⟩

theorem surjective_deletionClock {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) (hρ : ContDiff ℝ ∞ ρ) :
    Surjective (deletionClock ρ N) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact surjective_of_add_periods (by linarith : (0 : ℝ) < N)
    (by linarith : 0 < (N : ℝ) - 1)
    (contDiff_deletionClock N hδ hδhalf htail hbound hρ).continuous
    (fun t => by simpa only [add_sub_assoc] using
      deletionClock_add_period (N := N) ρ (by omega) t)


noncomputable def deletionClockDiffeomorph {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1) : ℝ ≃ₘ[ℝ] ℝ := by
  have hs := contDiff_deletionClock N hδ hδhalf htail hbound hρ
  have hp (t : ℝ) : 0 < deriv (deletionClock ρ N) t := by
    linarith [(deriv_deletionClock_mem_Icc hN hδ hδhalf htail hbound
      (hρ.differentiable (by simp)) hder t).1]
  let e : ℝ ≃ₜ ℝ :=
    (StrictMono.orderIsoOfSurjective (deletionClock ρ N)
      (strictMono_of_deriv_pos hp)
      (surjective_deletionClock hN hδ hδhalf htail hbound hρ)).toHomeomorph
  refine { toEquiv := e.toEquiv, contMDiff_toFun := hs.contMDiff, contMDiff_invFun := ?_ }
  exact (e.contDiff_symm_deriv (fun t => (hp t).ne')
    (fun t => (hs.differentiable (by simp) t).hasDerivAt) hs).contMDiff

@[simp] theorem deletionClockDiffeomorph_apply {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1) (t : ℝ) :
    deletionClockDiffeomorph hN hδ hδhalf htail hbound hρ hder t =
      deletionClock ρ N t := rfl

theorem deletionClockVertex_eq_self {N : ℕ} {j : ℤ} (hj : 0 ≤ j) (hjN : j + 1 < N) :
    deletionClockVertex N j = j := by
  have hn : (0 : ℤ) < N := by omega
  have hq (k : ℤ) (hk : 0 ≤ k) (hkN : k < N) : k / (N : ℤ) = 0 := by
    have hlo : 0 ≤ k / (N : ℤ) := by
      simpa using Int.ediv_le_ediv hn hk
    have hhi : k / (N : ℤ) < 1 := (Int.ediv_lt_iff_lt_mul hn).mpr (by simpa using hkN)
    omega
  simp only [deletionClockVertex, hq j hj (by omega), hq (j + 1) (by omega) hjN,
    Int.cast_zero, add_zero, zero_div, sub_zero]

theorem deletionClockVertex_last {N : ℕ} (hN : 2 ≤ N) :
    deletionClockVertex N (N - 1) = (N : ℝ) - 3 / 2 := by
  have hn : (0 : ℤ) < N := by omega
  have hq : ((N : ℤ) - 1) / N = 0 := by
    have hlo : 0 ≤ ((N : ℤ) - 1) / N := by
      simpa using Int.ediv_le_ediv hn (show 0 ≤ (N : ℤ) - 1 by omega)
    have hhi : ((N : ℤ) - 1) / N < 1 :=
      (Int.ediv_lt_iff_lt_mul hn).mpr (by omega)
    omega
  simp only [deletionClockVertex, hq, sub_add_cancel, Int.ediv_self hn.ne',
    Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_zero, zero_add]
  ring

theorem deletionClockVertex_neg_one {N : ℕ} (hN : 2 ≤ N) :
    deletionClockVertex N (-1) = -1 / 2 := by
  have h := deletionClockVertex_add_period (show 0 < N by omega) (-1)
  rw [show (-1 : ℤ) + N = N - 1 by omega, deletionClockVertex_last hN] at h
  linarith


theorem deletionClock_eq_self {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    {i : ℤ} (hi : 1 ≤ i) (hiN : i + 2 < N) {t : ℝ}
    (ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ)) :
    deletionClock ρ N t = t := by
  rw [deletionClock, roundedVertexPath_eq_local _ hδ hδhalf htail hbound i ht,
    deletionClockVertex_eq_self (by omega) (by omega),
    deletionClockVertex_eq_self (by omega) (by omega),
    deletionClockVertex_eq_self (by omega) (by omega)]
  simp only [roundedCorner, Int.cast_sub, Int.cast_one, Int.cast_add, smul_eq_mul]
  ring


theorem deletionClock_eq_at_zero {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 3 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) {t : ℝ}
    (ht : t ∈ Ioo (-1 + δ) (1 - δ)) :
    deletionClock ρ N t = (3 * t + ρ t) / 4 := by
  have ht' : t ∈ Ioo ((0 : ℤ) - 1 + δ) ((0 : ℤ) + 1 - δ) := by simpa using ht
  rw [deletionClock, roundedVertexPath_eq_local _ hδ hδhalf htail hbound 0 ht']
  norm_num only [sub_zero, zero_sub, zero_add] at *
  rw [deletionClockVertex_eq_self (by omega) (by omega),
    deletionClockVertex_neg_one (by omega), deletionClockVertex_eq_self (by omega) (by omega)]
  simp only [roundedCorner, Int.cast_zero, Int.cast_one, sub_zero, smul_eq_mul]
  ring


theorem deletionClock_eq_at_penultimate {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 4 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) {t : ℝ}
    (ht : t ∈ Ioo ((N : ℝ) - 3 + δ) ((N : ℝ) - 1 - δ)) :
    deletionClock ρ N t = (N : ℝ) - 2 +
      (3 * (t - ((N : ℝ) - 2)) - ρ (t - ((N : ℝ) - 2))) / 4 := by
  have ht' : t ∈ Ioo (((N : ℤ) - 2 : ℤ) - 1 + δ)
      (((N : ℤ) - 2 : ℤ) + 1 - δ) := by
    push_cast
    constructor <;> linarith [ht.1, ht.2]
  rw [deletionClock, roundedVertexPath_eq_local _ hδ hδhalf htail hbound ((N : ℤ) - 2) ht']
  rw [show (N : ℤ) - 2 + 1 = N - 1 by omega, deletionClockVertex_last (by omega),
    deletionClockVertex_eq_self (by omega) (by omega),
    deletionClockVertex_eq_self (by omega) (by omega)]
  simp only [roundedCorner, Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_ofNat,
    smul_eq_mul]
  ring


theorem deletionClock_eq_at_last {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 3 ≤ N)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) {t : ℝ}
    (ht : t ∈ Ioo ((N : ℝ) - 2 + δ) ((N : ℝ) - δ)) :
    deletionClock ρ N t = (t + (N : ℝ) - 2) / 2 := by
  have ht' : t ∈ Ioo (((N : ℤ) - 1 : ℤ) - 1 + δ)
      (((N : ℤ) - 1 : ℤ) + 1 - δ) := by
    push_cast
    constructor <;> linarith [ht.1, ht.2]
  have hzero : deletionClockVertex N 0 = 0 := by
    simpa only [Int.cast_zero] using
      deletionClockVertex_eq_self (N := N) (j := 0) (by omega) (by omega)
  have hNval : deletionClockVertex N N = (N : ℝ) - 1 := by
    simpa only [zero_add, hzero] using deletionClockVertex_add_period (show 0 < N by omega) 0
  rw [deletionClock, roundedVertexPath_eq_local _ hδ hδhalf htail hbound ((N : ℤ) - 1) ht']
  rw [sub_add_cancel, hNval, deletionClockVertex_last (by omega),
    deletionClockVertex_eq_self (by omega) (by omega)]
  simp only [roundedCorner, Int.cast_sub, Int.cast_natCast, Int.cast_one, smul_eq_mul]
  ring

end Poincare.Manifold.Schoenflies.Plane
