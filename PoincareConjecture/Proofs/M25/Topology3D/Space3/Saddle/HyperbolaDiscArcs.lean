import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import Mathlib.Tactic

set_option autoImplicit false

open Set Function
open scoped Matrix

namespace PoincareConjecture.M25.Topology3D

theorem saddle_hyperbola_disc_arcs
    (rho delta : ℝ) (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta < rho ^ 2) :
    let a := Real.sqrt ((rho ^ 2 - delta) / 2)
    let b := Real.sqrt ((rho ^ 2 + delta) / 2)
    let sign : Fin 2 → ℝ := ![1, -1]
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let other : Fin 2 → Fin 2 := ![1, 0]
    let v : unitInterval → ℝ := fun t => a * (1 - 2 * (t : ℝ))
    let lower : Fin 2 → unitInterval → (ℝ × ℝ) := fun i t =>
      (sign i * v t, sign i * Real.sqrt ((v t) ^ 2 + delta))
    let upper : Fin 2 → unitInterval → (ℝ × ℝ) := fun i t =>
      (sign i * Real.sqrt ((v t) ^ 2 + delta), sign i * v t)
    let pm : Fin 4 → (ℝ × ℝ) := fun i => (sx i * a, sy i * b)
    let pp : Fin 4 → (ℝ × ℝ) := fun i => (sx i * b, sy i * a)
    (∀ i : Fin 2,
      Continuous (lower i) ∧ Function.Injective (lower i) ∧
      Continuous (upper i) ∧ Function.Injective (upper i)) ∧
    Disjoint (range (lower 0)) (range (lower 1)) ∧
    {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} = ⋃ i : Fin 2, range (lower i) ∧
    {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} =
        ⋃ i : Fin 2, lower i '' Ioo (0 : unitInterval) 1 ∧
    {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} = ⋃ i : Fin 2, range (upper i) ∧
    ∀ i : Fin 2,
      lower i 0 = pm (ep (i, 0)) ∧ lower i 1 = pm (ep (i, 1)) ∧
      upper i 0 = pp (ep (i, 0)) ∧ upper i 1 = pp (ep (other i, 1)) := by
  classical
  let a := Real.sqrt ((rho ^ 2 - delta) / 2)
  let b := Real.sqrt ((rho ^ 2 + delta) / 2)
  let sign : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let other : Fin 2 → Fin 2 := ![1, 0]
  let v : unitInterval → ℝ := fun t => a * (1 - 2 * (t : ℝ))
  let lower : Fin 2 → unitInterval → (ℝ × ℝ) := fun i t =>
    (sign i * v t, sign i * Real.sqrt ((v t) ^ 2 + delta))
  let upper : Fin 2 → unitInterval → (ℝ × ℝ) := fun i t =>
    (sign i * Real.sqrt ((v t) ^ 2 + delta), sign i * v t)
  let pm : Fin 4 → (ℝ × ℝ) := fun i => (sx i * a, sy i * b)
  let pp : Fin 4 → (ℝ × ℝ) := fun i => (sx i * b, sy i * a)
  change (∀ i, Continuous (lower i) ∧ Injective (lower i) ∧
      Continuous (upper i) ∧ Injective (upper i)) ∧
    Disjoint (range (lower 0)) (range (lower 1)) ∧
    {s | s.1 ^ 2 - s.2 ^ 2 = -delta ∧ s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} =
      (⋃ i, range (lower i)) ∧
    {s | s.1 ^ 2 - s.2 ^ 2 = -delta ∧ s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} =
      (⋃ i, lower i '' Ioo (0 : unitInterval) 1) ∧
    {s | s.1 ^ 2 - s.2 ^ 2 = delta ∧ s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} =
      (⋃ i, range (upper i)) ∧
    ∀ i, lower i 0 = pm (ep (i, 0)) ∧ lower i 1 = pm (ep (i, 1)) ∧
      upper i 0 = pp (ep (i, 0)) ∧ upper i 1 = pp (ep (other i, 1))
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = (rho ^ 2 - delta) / 2 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (rho ^ 2 + delta) / 2 := Real.sq_sqrt (by positivity)
  have hsign (i : Fin 2) : (sign i) ^ 2 = 1 ∧ sign i ≠ 0 := by
    fin_cases i <;> norm_num [sign]
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hvbounds (t : unitInterval) : -a ≤ v t ∧ v t ≤ a := by
    dsimp [v]
    constructor <;> nlinarith [t.property.1, t.property.2]
  have hvstrict (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) :
      -a < v t ∧ v t < a := by
    have ht0 : 0 < (t : ℝ) := ht.1
    have ht1 : (t : ℝ) < 1 := ht.2
    dsimp [v]
    constructor <;> nlinarith
  have hvinj : Injective v := by
    intro s t hst
    apply Subtype.ext
    dsimp [v] at hst
    nlinarith
  have hsmooth (i : Fin 2) : Continuous (lower i) ∧ Injective (lower i) ∧
      Continuous (upper i) ∧ Injective (upper i) := by
    have hr : Continuous (fun t : unitInterval => Real.sqrt ((v t) ^ 2 + delta)) :=
      ((hv.pow 2).add continuous_const).sqrt
    refine ⟨(continuous_const.mul hv).prodMk (continuous_const.mul hr), ?_,
      (continuous_const.mul hr).prodMk (continuous_const.mul hv), ?_⟩
    · intro s t hst
      exact hvinj (mul_left_cancel₀ (hsign i).2 (congrArg Prod.fst hst))
    · intro s t hst
      exact hvinj (mul_left_cancel₀ (hsign i).2 (congrArg Prod.snd hst))
  have hswap (i : Fin 2) (t : unitInterval) : upper i t = (lower i t).swap := rfl
  have hlower (i : Fin 2) (t : unitInterval) :
      (lower i t).1 ^ 2 - (lower i t).2 ^ 2 = -delta ∧
      (lower i t).1 ^ 2 + (lower i t).2 ^ 2 ≤ rho ^ 2 := by
    have hroot := Real.sq_sqrt (by positivity : 0 ≤ (v t) ^ 2 + delta)
    have hvsq : (v t) ^ 2 ≤ a ^ 2 := by
      have hh := hvbounds t
      nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (by linarith : 0 ≤ a + v t)]
    dsimp [lower]
    simp only [mul_pow, (hsign i).1, one_mul]
    constructor <;> nlinarith
  have hlower_strict (i : Fin 2) (t : unitInterval)
      (ht : t ∈ Ioo (0 : unitInterval) 1) :
      (lower i t).1 ^ 2 + (lower i t).2 ^ 2 < rho ^ 2 := by
    have hroot := Real.sq_sqrt (by positivity : 0 ≤ (v t) ^ 2 + delta)
    have hvsq : (v t) ^ 2 < a ^ 2 := by
      have hh := hvstrict t ht
      nlinarith [mul_pos (sub_pos.mpr hh.2) (by linarith : 0 < a + v t)]
    dsimp [lower]
    simp only [mul_pow, (hsign i).1, one_mul]
    nlinarith
  have hdisjoint : Disjoint (range (lower 0)) (range (lower 1)) := by
    apply disjoint_left.mpr
    rintro p ⟨s, rfl⟩ ⟨t, hts⟩
    have hs : 0 < Real.sqrt ((v s) ^ 2 + delta) := Real.sqrt_pos.2 (by positivity)
    have ht : 0 < Real.sqrt ((v t) ^ 2 + delta) := Real.sqrt_pos.2 (by positivity)
    have hh := congrArg Prod.snd hts
    norm_num [lower, sign] at hh
    linarith
  have hinverse (s : ℝ × ℝ)
      (hq : s.1 ^ 2 - s.2 ^ 2 = -delta)
      (hr : s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2) :
      ∃ (i : Fin 2) (t : unitInterval), lower i t = s ∧
        (s.1 ^ 2 + s.2 ^ 2 < rho ^ 2 → t ∈ Ioo (0 : unitInterval) 1) := by
    have hy : s.2 ≠ 0 := by intro hh; rw [hh] at hq; nlinarith [sq_nonneg s.1]
    let i : Fin 2 := if 0 < s.2 then 0 else 1
    have hiy : 0 < sign i * s.2 := by
      by_cases hh : 0 < s.2
      · simp [i, hh, sign]
      · have hn : s.2 < 0 := lt_of_le_of_ne (le_of_not_gt hh) hy
        simpa [i, hh, sign] using neg_pos.mpr hn
    let w := sign i * s.1
    have hw2 : w ^ 2 = s.1 ^ 2 := by dsimp [w]; rw [mul_pow, (hsign i).1, one_mul]
    have hwabs : |w| ≤ a := by
      apply (sq_le_sq₀ (abs_nonneg w) ha.le).mp
      rw [sq_abs, hw2]
      nlinarith
    have hw := abs_le.mp hwabs
    have hdiv0 : -1 ≤ w / a := (le_div_iff₀ ha).mpr (by nlinarith [hw.1])
    have hdiv1 : w / a ≤ 1 := (div_le_iff₀ ha).mpr (by nlinarith [hw.2])
    let t : unitInterval := ⟨(1 - w / a) / 2, by constructor <;> linarith⟩
    have hvt : v t = w := by
      dsimp [v, t]
      field_simp [ha.ne']
      ring
    have hroot : Real.sqrt (w ^ 2 + delta) = sign i * s.2 := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hiy.le).mp
      rw [Real.sq_sqrt (by positivity), hw2, mul_pow, (hsign i).1, one_mul]
      linarith
    have hrec : lower i t = s := by
      apply Prod.ext
      · change sign i * v t = s.1
        rw [hvt]
        calc
          sign i * w = (sign i) ^ 2 * s.1 := by dsimp [w]; ring
          _ = s.1 := by rw [(hsign i).1, one_mul]
      · change sign i * Real.sqrt ((v t) ^ 2 + delta) = s.2
        rw [hvt, hroot]
        calc
          sign i * (sign i * s.2) = (sign i) ^ 2 * s.2 := by ring
          _ = s.2 := by rw [(hsign i).1, one_mul]
    refine ⟨i, t, hrec, ?_⟩
    intro hrs
    have hwa : |w| < a := by
      apply (sq_lt_sq₀ (abs_nonneg w) ha.le).mp
      rw [sq_abs, hw2]
      nlinarith
    have hws := abs_lt.mp hwa
    have hd0 : -1 < w / a := (lt_div_iff₀ ha).mpr (by nlinarith [hws.1])
    have hd1 : w / a < 1 := (div_lt_iff₀ ha).mpr (by nlinarith [hws.2])
    change 0 < (1 - w / a) / 2 ∧ (1 - w / a) / 2 < 1
    constructor <;> linarith
  have hclosed : {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} = ⋃ i : Fin 2, range (lower i) := by
    ext s
    constructor
    · intro hs
      obtain ⟨i, t, ht, _⟩ := hinverse s hs.1 hs.2
      exact mem_iUnion.mpr ⟨i, ⟨t, ht⟩⟩
    · intro hs
      obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hs
      exact hlower i t
  have hopen : {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} =
        ⋃ i : Fin 2, lower i '' Ioo (0 : unitInterval) 1 := by
    ext s
    constructor
    · intro hs
      obtain ⟨i, t, ht, hti⟩ := hinverse s hs.1 hs.2.le
      exact mem_iUnion.mpr ⟨i, ⟨t, hti hs.2, ht⟩⟩
    · intro hs
      obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hs
      exact ⟨(hlower i t).1, hlower_strict i t ht⟩
  have hupper : {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} = ⋃ i : Fin 2, range (upper i) := by
    ext s
    constructor
    · intro hs
      obtain ⟨i, t, ht, _⟩ := hinverse s.swap (by dsimp; linarith [hs.1])
        (by dsimp; linarith [hs.2])
      refine mem_iUnion.mpr ⟨i, ⟨t, ?_⟩⟩
      rw [hswap, ht, Prod.swap_swap]
    · intro hs
      obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hs
      rw [hswap]
      have hh := hlower i t
      change (lower i t).2 ^ 2 - (lower i t).1 ^ 2 = delta ∧
        (lower i t).2 ^ 2 + (lower i t).1 ^ 2 ≤ rho ^ 2
      constructor <;> linarith [hh.1, hh.2]
  have habroot : Real.sqrt (a ^ 2 + delta) = b := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hb.le).mp
    rw [Real.sq_sqrt (by positivity)]
    linarith
  refine ⟨hsmooth, hdisjoint, hclosed, hopen, hupper, ?_⟩
  intro i
  fin_cases i <;>
    norm_num [lower, upper, pm, pp, v, sign, sx, sy, ep, other, habroot, finProdFinEquiv]

end PoincareConjecture.M25.Topology3D
