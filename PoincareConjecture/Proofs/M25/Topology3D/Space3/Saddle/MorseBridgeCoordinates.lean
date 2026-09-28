import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.AmbientMorseChart
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "C3" => ((ℝ × ℝ) × ℝ)

noncomputable def morseBridgeDiffeomorph (c ε : ℝ) (hε : 0 < ε) :
    Diffeomorph 𝓘(ℝ, C3) 𝓘(ℝ, C3) C3 C3 ∞ := by
  let d (t : ℝ) := ε + t ^ 2
  let q (t : ℝ) := Real.sqrt (d t)
  have hd (t : ℝ) : 0 < d t := add_pos_of_pos_of_nonneg hε (sq_nonneg t)
  have hq (t : ℝ) : 0 < q t := Real.sqrt_pos.mpr (hd t)
  have hq2 (t : ℝ) : q t ^ 2 = d t := Real.sq_sqrt (hd t).le
  have hds : ContDiff ℝ ∞ d := contDiff_const.add (contDiff_id.pow 2)
  have hqs : ContDiff ℝ ∞ q := hds.sqrt (fun t => (hd t).ne')
  let F (p : C3) := ((q p.2 * p.1.1, p.2),
    c + d p.2 * (p.1.2 + p.1.1 ^ 2) - p.2 ^ 2)
  let G (p : C3) := ((p.1.1 / q p.1.2,
    (p.2 - c - p.1.1 ^ 2 + p.1.2 ^ 2) / d p.1.2), p.1.2)
  have hF : ContDiff ℝ ∞ F :=
    (((hqs.comp contDiff_snd).mul contDiff_fst.fst).prodMk contDiff_snd).prodMk
      ((contDiff_const.add ((hds.comp contDiff_snd).mul
        (contDiff_fst.snd.add (contDiff_fst.fst.pow 2)))).sub (contDiff_snd.pow 2))
  have hG : ContDiff ℝ ∞ G :=
    ((contDiff_fst.fst.div (hqs.comp contDiff_fst.snd) (fun p => (hq p.1.2).ne')).prodMk
      ((((contDiff_snd.sub contDiff_const).sub (contDiff_fst.fst.pow 2)).add
        (contDiff_fst.snd.pow 2)).div (hds.comp contDiff_fst.snd)
        (fun p => (hd p.1.2).ne'))).prodMk contDiff_fst.snd
  exact {
    toEquiv := {
      toFun := F
      invFun := G
      left_inv := by
        rintro ⟨⟨x, r⟩, t⟩
        apply Prod.ext
        · apply Prod.ext
          · change q t * x / q t = x
            field_simp [(hq t).ne']
          · change (c + d t * (r + x ^ 2) - t ^ 2 - c -
              (q t * x) ^ 2 + t ^ 2) / d t = r
            apply (div_eq_iff (hd t).ne').mpr
            rw [mul_pow, hq2]
            ring
        · rfl
      right_inv := by
        rintro ⟨⟨s, t⟩, z⟩
        apply Prod.ext
        · apply Prod.ext
          · change q t * (s / q t) = s
            field_simp [(hq t).ne']
          · rfl
        · change c + d t * ((z - c - s ^ 2 + t ^ 2) / d t +
            (s / q t) ^ 2) - t ^ 2 = z
          have hx : d t * (s / q t) ^ 2 = s ^ 2 := by
            rw [div_pow, ← hq2]
            field_simp [(hq t).ne']
          have hz : d t * ((z - c - s ^ 2 + t ^ 2) / d t) =
              z - c - s ^ 2 + t ^ 2 := by field_simp [(hd t).ne']
          rw [mul_add, hx, hz]
          ring }
    contMDiff_toFun := hF.contMDiff
    contMDiff_invFun := hG.contMDiff }

variable (c ε : ℝ) (hε : 0 < ε)
local notation "F" => morseBridgeDiffeomorph c ε hε

theorem morseBridgeDiffeomorph_apply (p : C3) :
    F p = ((Real.sqrt (ε + p.2 ^ 2) * p.1.1, p.2),
      c + (ε + p.2 ^ 2) * (p.1.2 + p.1.1 ^ 2) - p.2 ^ 2) := rfl

theorem morseBridgeDiffeomorph_symm_apply (p : C3) :
    (F).symm p = ((p.1.1 / Real.sqrt (ε + p.1.2 ^ 2),
      (p.2 - c - p.1.1 ^ 2 + p.1.2 ^ 2) / (ε + p.1.2 ^ 2)), p.1.2) := rfl

theorem morseBridgeDiffeomorph_residuals (p : C3) :
    (F p).1.2 = p.2 ∧
      (F p).2 - c - (F p).1.1 ^ 2 + p.2 ^ 2 = (ε + p.2 ^ 2) * p.1.2 ∧
      c + ε - (F p).2 = (ε + p.2 ^ 2) * (1 - p.1.2 - p.1.1 ^ 2) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [morseBridgeDiffeomorph_apply, mul_pow,
      Real.sq_sqrt (show 0 ≤ ε + p.2 ^ 2 by positivity)]
    ring
  · simp only [morseBridgeDiffeomorph_apply]
    ring

theorem morseBridgeDiffeomorph_image_lens (β : ℝ) (_hβ : 0 ≤ β) :
    F '' {p : C3 | 0 ≤ p.1.2 ∧ p.1.1 ^ 2 + p.1.2 ≤ 1 ∧ |p.2| ≤ β} =
      {p : C3 | |p.1.2| ≤ β ∧ c + p.1.1 ^ 2 - p.1.2 ^ 2 ≤ p.2 ∧ p.2 ≤ c + ε} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨ht, hr, hz⟩ := morseBridgeDiffeomorph_residuals c ε hε p
    have hd : 0 < ε + p.2 ^ 2 := by positivity
    refine ⟨by simpa only [ht] using hp.2.2, ?_, ?_⟩
    · rw [ht]
      nlinarith [mul_nonneg hd.le hp.1]
    · nlinarith [mul_nonneg hd.le (show 0 ≤ 1 - p.1.2 - p.1.1 ^ 2 by
        linarith [hp.2.1])]
  · intro hy
    let p := (F).symm y
    have heq : F p = y := (F).apply_symm_apply y
    obtain ⟨ht, hr, hz⟩ := morseBridgeDiffeomorph_residuals c ε hε p
    rw [heq] at ht hr hz
    change |y.1.2| ≤ β ∧ c + y.1.1 ^ 2 - y.1.2 ^ 2 ≤ y.2 ∧ y.2 ≤ c + ε at hy
    rw [ht] at hy
    have hd : 0 < ε + p.2 ^ 2 := by positivity
    refine ⟨p, ⟨?_, ?_, ?_⟩, heq⟩
    · apply (mul_nonneg_iff_of_pos_left hd).mp
      nlinarith [hy.2.1]
    · have hh : 0 ≤ 1 - p.1.2 - p.1.1 ^ 2 :=
        (mul_nonneg_iff_of_pos_left hd).mp (by linarith [hy.2.2])
      linarith
    · exact hy.1

theorem morseBridgeDiffeomorph_buffer_bounds {δ B : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (p : C3) (hp : -δ ≤ p.1.2 ∧ p.1.1 ^ 2 + p.1.2 ≤ 1 + δ ∧ |p.2| ≤ B) :
    (F p).1.1 ^ 2 + (F p).1.2 ^ 2 ≤ (ε + B ^ 2) * (1 + 2 * δ) + B ^ 2 ∧
      (F p).2 - c ≤ ε + δ * (ε + B ^ 2) ∧
      c - (F p).2 ≤ B ^ 2 + δ * (ε + B ^ 2) := by
  have ht2 : p.2 ^ 2 ≤ B ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg p.2) hB).mpr hp.2.2
    simpa only [sq_abs] using hh
  have hx2 : p.1.1 ^ 2 ≤ 1 + 2 * δ := by linarith [hp.1, hp.2.1]
  have hd : 0 ≤ ε + p.2 ^ 2 := by positivity
  have hdd : ε + p.2 ^ 2 ≤ ε + B ^ 2 := by linarith
  have hprod := mul_le_mul hdd hx2 (sq_nonneg p.1.1)
    (show 0 ≤ ε + B ^ 2 by positivity)
  have hu := mul_le_mul_of_nonneg_left
    (show p.1.2 + p.1.1 ^ 2 - 1 ≤ δ by linarith [hp.2.1]) hd
  have hl := mul_le_mul_of_nonneg_left
    (show -(p.1.2 + p.1.1 ^ 2) ≤ δ by nlinarith [hp.1, sq_nonneg p.1.1]) hd
  have hδd := mul_le_mul_of_nonneg_right hdd hδ
  simp only [morseBridgeDiffeomorph_apply, mul_pow, Real.sq_sqrt hd]
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

noncomputable def morseBridgeChart (A : OpenPartialHomeomorph C3 E3) :
    OpenPartialHomeomorph C3 E3 := (F).toHomeomorph.toOpenPartialHomeomorph.trans A

variable (A : OpenPartialHomeomorph C3 E3)
local notation "Bridge" => morseBridgeChart c ε hε A

theorem morseBridgeChart_source_target :
    (Bridge).source = F ⁻¹' A.source ∧ (Bridge).target = A.target := by
  constructor <;> ext p <;> simp [morseBridgeChart]

theorem morseBridgeChart_smooth (hA : ContDiffOn ℝ ∞ A A.source)
    (hi : ContDiffOn ℝ ∞ A.symm A.target) :
    ContDiffOn ℝ ∞ Bridge (Bridge).source ∧
      ContDiffOn ℝ ∞ (Bridge).symm (Bridge).target := by
  refine ⟨hA.comp (F).contDiff.contDiffOn (fun _ hp => hp.2), ?_⟩
  exact (F).symm.contDiff.comp_contDiffOn (hi.mono inter_subset_left)

theorem morseBridgeChart_identities (H : E3 →L[ℝ] ℝ) (S : Set E3)
    (hH : ∀ q ∈ A.source, H (A q) = q.2)
    (hS : ∀ q ∈ A.source, A q ∈ S ↔ q.2 = c + q.1.1 ^ 2 - q.1.2 ^ 2)
    (p : C3) (hp : p ∈ (Bridge).source) :
    H (Bridge p) = c + (ε + p.2 ^ 2) * (p.1.2 + p.1.1 ^ 2) - p.2 ^ 2 ∧
      (Bridge p ∈ S ↔ p.1.2 = 0) ∧
      (H (Bridge p) = c + ε ↔ p.1.2 + p.1.1 ^ 2 = 1) := by
  have hpa : F p ∈ A.source := hp.2
  have hheight : H (Bridge p) = (F p).2 := hH _ hpa
  have hmem : Bridge p ∈ S ↔ (F p).2 = c + (F p).1.1 ^ 2 - (F p).1.2 ^ 2 := hS _ hpa
  obtain ⟨ht, hr, hz⟩ := morseBridgeDiffeomorph_residuals c ε hε p
  have hd : 0 < ε + p.2 ^ 2 := by positivity
  refine ⟨hheight, ?_, ?_⟩
  · rw [hmem, ht]
    constructor
    · intro heq
      have hzprod : (ε + p.2 ^ 2) * p.1.2 = 0 := by linarith
      exact (mul_eq_zero.mp hzprod).resolve_left hd.ne'
    · intro heq
      rw [heq, mul_zero] at hr
      linarith
  · rw [hheight]
    constructor
    · intro heq
      have hzprod : (ε + p.2 ^ 2) * (1 - p.1.2 - p.1.1 ^ 2) = 0 := by linarith
      have hh := (mul_eq_zero.mp hzprod).resolve_left hd.ne'
      linarith
    · intro heq
      have hh : 1 - p.1.2 - p.1.1 ^ 2 = 0 := by linarith
      rw [hh, mul_zero] at hz
      linarith

theorem morseBridgeChart_buffer_subset_source {R h δ B β : ℝ}
    (hA : {q : C3 | q.1.1 ^ 2 + q.1.2 ^ 2 ≤ R ^ 2 ∧ |q.2 - c| ≤ h} ⊆ A.source)
    (hδ : 0 < δ) (hβ : 0 < β) (hβB : β < B)
    (hR : (ε + B ^ 2) * (1 + 2 * δ) + B ^ 2 < R ^ 2)
    (hu : ε + δ * (ε + B ^ 2) < h) (hl : B ^ 2 + δ * (ε + B ^ 2) < h) :
    {p : C3 | -δ ≤ p.1.2 ∧ p.1.1 ^ 2 + p.1.2 ≤ 1 + δ ∧ |p.2| ≤ B} ⊆ (Bridge).source ∧
      {p : C3 | 0 ≤ p.1.2 ∧ p.1.1 ^ 2 + p.1.2 ≤ 1 ∧ |p.2| ≤ β} ⊆
        {p : C3 | -δ < p.1.2 ∧ p.1.1 ^ 2 + p.1.2 < 1 + δ ∧ |p.2| < B} := by
  constructor
  · intro p hp
    obtain ⟨hr, hz, hc⟩ := morseBridgeDiffeomorph_buffer_bounds c ε hε hδ.le
      (hβ.trans hβB).le p hp
    refine ⟨mem_univ _, ?_⟩
    change F p ∈ A.source
    exact hA ⟨hr.trans hR.le, abs_le.mpr
      ⟨by linarith [hc.trans_lt hl], hz.trans hu.le⟩⟩
  · intro p hp
    exact ⟨by linarith [hp.1], by linarith [hp.2.1], hp.2.2.trans_lt hβB⟩

end PoincareConjecture.M25.Topology3D
