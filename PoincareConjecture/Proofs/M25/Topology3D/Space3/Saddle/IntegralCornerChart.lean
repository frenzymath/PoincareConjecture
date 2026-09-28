import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic











set_option autoImplicit false

open Set Function MeasureTheory
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_integral_corner_chart :
    let z : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
    let Z : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, z s
    let a : ℝ := 1 - Z 1
    let b : ℝ := Z 1
    let C : ℝ → ℝ × ℝ := fun t => (a - t + Z t, Z t)
    ∃ Q : Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞,
      a ∈ Icc (1 / 3 : ℝ) (2 / 3) ∧
      b ∈ Icc (1 / 3 : ℝ) (2 / 3) ∧ a + b = 1 ∧
      ContDiff ℝ ∞ C ∧ Function.Injective C ∧
      (∀ t : ℝ, HasDerivAt C (z t - 1, z t) t ∧ deriv C t ≠ 0) ∧
      (∀ t : ℝ, t ≤ 1 / 3 → C t = (a - t, 0)) ∧
      (∀ t : ℝ, 2 / 3 ≤ t → C t = (0, t - a)) ∧
      Set.MapsTo C (Icc (0 : ℝ) 1) (Icc 0 a ×ˢ Icc 0 b) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, C t ≠ 0) ∧
      (∀ p : ℝ × ℝ, Q p = ((C p.1).1 + p.2, (C p.1).2 + p.2)) ∧
      ∀ p : ℝ × ℝ,
        Q.symm p = (p.2 - p.1 + a, p.2 - Z (p.2 - p.1 + a)) := by
  classical
  let z : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  let Z : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, z s
  let a : ℝ := 1 - Z 1
  let b : ℝ := Z 1
  let C : ℝ → ℝ × ℝ := fun t => (a - t + Z t, Z t)
  have hz : ContDiff ℝ ∞ z := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hzr (t : ℝ) : 0 ≤ z t ∧ z t ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hz0 (t : ℝ) (ht : t ≤ 1 / 3) : z t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hz1 (t : ℝ) (ht : 2 / 3 ≤ t) : z t = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hzi (s t : ℝ) : IntervalIntegrable z volume s t := hz.continuous.intervalIntegrable s t
  have hZd (t : ℝ) : HasDerivAt Z (z t) t :=
    intervalIntegral.integral_hasDerivAt_right (hzi 0 t)
      hz.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hz.continuous.continuousAt
  have hZ : ContDiff ℝ ∞ Z := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun t => (hZd t).differentiableAt, ?_⟩
    have heq : deriv Z = z := funext fun t => (hZd t).deriv
    rw [heq]
    exact hz
  have hleft (t : ℝ) : a - t + Z t = ∫ s in t..(1 : ℝ), (1 - z s) := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable t 1) (hzi t 1)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    have hs : Z t + (∫ s in t..(1 : ℝ), z s) = Z 1 :=
      intervalIntegral.integral_add_adjacent_intervals (hzi 0 t) (hzi t 1)
    dsimp only [a]
    linarith
  have hZhead (t : ℝ) (ht : t ≤ 1 / 3) : Z t = 0 := by
    change (∫ s in (0 : ℝ)..t, z s) = 0
    calc
      _ = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        apply hz0
        rcases le_total (0 : ℝ) t with h | h
        · rw [uIcc_of_le h] at hs
          exact hs.2.trans ht
        · rw [uIcc_of_ge h] at hs
          linarith [hs.2]
      _ = 0 := by simp
  have hhead (t : ℝ) (ht : t ≤ 1 / 3) : C t = (a - t, 0) := by
    simp only [C, hZhead t ht, add_zero]
  have htail (t : ℝ) (ht : 2 / 3 ≤ t) : C t = (0, t - a) := by
    have hi : (∫ s in t..(1 : ℝ), (1 - z s)) = 0 := by
      calc
        _ = ∫ s in t..(1 : ℝ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hs0 : 2 / 3 ≤ s := by
            rcases le_total t (1 : ℝ) with h | h
            · rw [uIcc_of_le h] at hs
              exact ht.trans hs.1
            · rw [uIcc_of_ge h] at hs
              linarith [hs.1]
          change 1 - z s = 0
          rw [hz1 s hs0, sub_self]
        _ = 0 := by simp
    have he := (hleft t).trans hi
    apply Prod.ext
    · exact he
    · change Z t = t - a
      linarith
  have hnonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ (C t).1 ∧ 0 ≤ (C t).2 := by
    constructor
    · change 0 ≤ a - t + Z t
      rw [hleft]
      exact intervalIntegral.integral_nonneg_of_forall ht.2 (fun s => sub_nonneg.mpr (hzr s).2)
    · exact intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => (hzr s).1)
  have ha : a ∈ Icc (1 / 3 : ℝ) (2 / 3) := by
    have hl := (hnonneg (1 / 3) ⟨by norm_num, by norm_num⟩).1
    have hu := (hnonneg (2 / 3) ⟨by norm_num, by norm_num⟩).2
    rw [hhead (1 / 3) le_rfl] at hl
    rw [htail (2 / 3) le_rfl] at hu
    change 0 ≤ a - 1 / 3 at hl
    change 0 ≤ 2 / 3 - a at hu
    exact ⟨by linarith, by linarith⟩
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hb : b ∈ Icc (1 / 3 : ℝ) (2 / 3) := ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have hC : ContDiff ℝ ∞ C := ((contDiff_const.sub contDiff_id).add hZ).prodMk hZ
  have hCd (t : ℝ) : HasDerivAt C (z t - 1, z t) t := by
    have hd : HasDerivAt (fun s : ℝ => a - s + Z s) (z t - 1) t := by
      convert! ((hasDerivAt_const t a).sub (hasDerivAt_id t)).add (hZd t) using 1
      ring
    exact hd.prodMk (hZd t)
  have hCreg (t : ℝ) : deriv C t ≠ 0 := by
    rw [(hCd t).deriv]
    intro heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    change z t - 1 = 0 at h1
    change z t = 0 at h2
    linarith
  have hCi : Injective C := by
    intro s t hst
    have h1 := congrArg Prod.fst hst
    have h2 := congrArg Prod.snd hst
    change a - s + Z s = a - t + Z t at h1
    change Z s = Z t at h2
    linarith
  have hrect : MapsTo C (Icc (0 : ℝ) 1) (Icc 0 a ×ˢ Icc 0 b) := by
    intro t ht
    have hZle : Z t ≤ t := by
      have hh := intervalIntegral.integral_mono_on ht.1 (hzi 0 t)
        (continuous_const.intervalIntegrable 0 t) (fun s _ => (hzr s).2)
      simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] using hh
    have htail0 : 0 ≤ ∫ s in t..(1 : ℝ), z s :=
      intervalIntegral.integral_nonneg_of_forall ht.2 (fun s => (hzr s).1)
    have hadd : Z t + (∫ s in t..(1 : ℝ), z s) = b :=
      intervalIntegral.integral_add_adjacent_intervals (hzi 0 t) (hzi t 1)
    exact ⟨⟨(hnonneg t ht).1, by change a - t + Z t ≤ a; linarith⟩,
      ⟨(hnonneg t ht).2, by change Z t ≤ b; linarith⟩⟩
  have hhalf0 : 0 < z (1 / 2) := Real.smoothTransition.pos_of_pos (by norm_num)
  have hhalf1 : z (1 / 2) < 1 := Real.smoothTransition.lt_one_of_lt_one (by norm_num)
  have havoid (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : C t ≠ 0 := by
    intro heq
    by_cases hh : t ≤ 1 / 2
    · have hp : 0 < ∫ s in t..(1 : ℝ), (1 - z s) :=
        intervalIntegral.integral_pos (by linarith)
          (continuous_const.sub hz.continuous).continuousOn
          (fun s _ => sub_nonneg.mpr (hzr s).2)
          ⟨1 / 2, ⟨hh, by norm_num⟩, sub_pos.mpr hhalf1⟩
      have hzero := congrArg Prod.fst heq
      change a - t + Z t = 0 at hzero
      rw [hleft] at hzero
      exact hp.ne' hzero
    · have hp : 0 < Z t := intervalIntegral.integral_pos (by linarith)
        hz.continuous.continuousOn (fun s _ => (hzr s).1)
        ⟨1 / 2, ⟨by norm_num, (lt_of_not_ge hh).le⟩, hhalf0⟩
      exact hp.ne' (congrArg Prod.snd heq)
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (a - p.1 + Z p.1 + p.2, Z p.1 + p.2)
  let g : ℝ × ℝ → ℝ × ℝ := fun p => (p.2 - p.1 + a, p.2 - Z (p.2 - p.1 + a))
  have hf : ContDiff ℝ ∞ f :=
    (((contDiff_const.sub contDiff_fst).add (hZ.comp contDiff_fst)).add contDiff_snd).prodMk
      ((hZ.comp contDiff_fst).add contDiff_snd)
  have hg : ContDiff ℝ ∞ g :=
    ((contDiff_snd.sub contDiff_fst).add contDiff_const).prodMk
      (contDiff_snd.sub (hZ.comp ((contDiff_snd.sub contDiff_fst).add contDiff_const)))
  have hgf (p : ℝ × ℝ) : g (f p) = p := by
    have ht : Z p.1 + p.2 - (a - p.1 + Z p.1 + p.2) + a = p.1 := by ring
    dsimp only [g, f]
    rw [ht]
    apply Prod.ext
    · rfl
    · ring
  have hfg (p : ℝ × ℝ) : f (g p) = p := by
    dsimp only [f, g]
    apply Prod.ext <;> ring
  let Q : Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ := {
    toEquiv := { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg }
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := hg.contMDiff }
  exact ⟨Q, ha, hb, hab, hC, hCi, fun t => ⟨hCd t, hCreg t⟩,
    hhead, htail, hrect, havoid, fun _ => rfl, fun _ => rfl⟩

end PoincareConjecture.M25.Topology3D
