import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_nonnested_reference_source_velocity
    (a : ℝ) (ha : 0 < a) (haLarge : 256 < a ^ 2) :
    let b : ℝ := 1 / (128 * a ^ 2)
    let I : Set ℝ := Ioo (-4 * b) (4 * b)
    let r : ℝ → ℝ := fun h => Real.sqrt (1 / 4 + h)
    let theta : ℝ → ℝ → ℝ := fun h R =>
      Real.arccos (Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h)
    let A : ℝ → ℝ := fun h => 2 * Real.pi - 2 * theta h 1
    let phi : ℝ × ℝ → ℝ := fun z => theta z.2 1 + A z.2 * z.1
    let U : Set (ℝ × ℝ) := {z | z.2 ∈ I ∧
      theta z.2 (1 / 4) < phi z ∧ phi z < 2 * Real.pi - theta z.2 (1 / 4)}
    let tR : ℝ → ℝ → ℝ := fun h R => (theta h R - theta h 1) / A h
    let D : Set (ℝ × ℝ) :=
      Icc (29 / 32 : ℝ) (35 / 32) ×ˢ Icc (-3 * b) (3 * b)
    let K0 : Set (ℝ × ℝ) :=
      (Icc (0 : ℝ) 1 ×ˢ Icc (-3 * b) (3 * b)) ∪
        ((fun p : ℝ × ℝ => (tR p.2 p.1, p.2)) '' D) ∪
        ((fun p : ℝ × ℝ => (1 - tR p.2 p.1, p.2)) '' D)
    IsOpen U ∧ IsCompact K0 ∧ K0 ⊆ U ∧
    ∃ v : (ℝ × ℝ) → ℝ,
      ContDiffOn ℝ ∞ v U ∧
      (∀ h ∈ I, ∀ t ∈ Icc (0 : ℝ) 1, (t, h) ∈ U) ∧
      (∀ h ∈ I, v (0, h) = 0 ∧ v (1, h) = 0) ∧
      ∀ R ∈ Ioo (7 / 8 : ℝ) (9 / 8), ∀ h ∈ I,
        (tR h R, h) ∈ U ∧ (1 - tR h R, h) ∈ U ∧
        HasDerivAt (fun h' : ℝ => (tR h' R, h')) (v (tR h R, h), 1) h ∧
        HasDerivAt (fun h' : ℝ => (1 - tR h' R, h'))
          (v (1 - tR h R, h), 1) h := by
  classical
  let b : ℝ := 1 / (128 * a ^ 2)
  let I : Set ℝ := Ioo (-4 * b) (4 * b)
  let r : ℝ → ℝ := fun h => Real.sqrt (1 / 4 + h)
  let theta : ℝ → ℝ → ℝ := fun h R =>
    Real.arccos (Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h)
  let A : ℝ → ℝ := fun h => 2 * Real.pi - 2 * theta h 1
  let phi : ℝ × ℝ → ℝ := fun z => theta z.2 1 + A z.2 * z.1
  let U : Set (ℝ × ℝ) := {z | z.2 ∈ I ∧
    theta z.2 (1 / 4) < phi z ∧ phi z < 2 * Real.pi - theta z.2 (1 / 4)}
  let tR : ℝ → ℝ → ℝ := fun h R => (theta h R - theta h 1) / A h
  let D : Set (ℝ × ℝ) :=
    Icc (29 / 32 : ℝ) (35 / 32) ×ˢ Icc (-3 * b) (3 * b)
  let K0 : Set (ℝ × ℝ) :=
    (Icc (0 : ℝ) 1 ×ˢ Icc (-3 * b) (3 * b)) ∪
      ((fun p : ℝ × ℝ => (tR p.2 p.1, p.2)) '' D) ∪
      ((fun p : ℝ × ℝ => (1 - tR p.2 p.1, p.2)) '' D)
  let e : ℝ := 1 / a ^ 2
  let J : Set ℝ := Ioo (1 / 5 : ℝ) (5 / 4)
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have he : 0 < e := by dsimp [e]; positivity
  have heSmall : e < 1 / 256 := by
    dsimp [e]
    rw [div_lt_iff₀ ha2]
    linarith only [haLarge]
  have hb : 0 < b := by dsimp [b]; positivity
  have hb4 : 4 * b = e / 32 := by dsimp [b, e]; ring
  have hdiv (x : ℝ) : x / a ^ 2 = x * e := by dsimp [e]; ring
  have hI (h : ℝ) (hh : h ∈ I) : -e / 32 < h ∧ h < e / 32 := by
    constructor <;> linarith only [hh.1, hh.2, hb4]
  have h3 (h : ℝ) (hh : h ∈ Icc (-3 * b) (3 * b)) : h ∈ I :=
    ⟨by linarith only [hh.1, hb], by linarith only [hh.2, hb]⟩
  have hRj (R : ℝ) (hR : R ∈ Ioo (7 / 8 : ℝ) (9 / 8)) : R ∈ J :=
    ⟨by linarith only [hR.1], by linarith only [hR.2]⟩
  have hj1 : (1 : ℝ) ∈ J := by norm_num [J]
  have hj4 : (1 / 4 : ℝ) ∈ J := by norm_num [J]
  have hr (h : ℝ) (hh : h ∈ I) :
      0 < r h ∧ (r h) ^ 2 = 1 / 4 + h ∧ ContDiffAt ℝ ∞ r h := by
    have hp : 0 < 1 / 4 + h := by linarith only [(hI h hh).1, heSmall]
    exact ⟨Real.sqrt_pos.mpr hp, Real.sq_sqrt hp.le,
      (contDiffAt_const.add contDiffAt_id).sqrt hp.ne'⟩
  have hscale (R : ℝ) (hR : R ∈ J) :
      e / 25 < R ^ 2 / a ^ 2 ∧ R ^ 2 / a ^ 2 < 25 / 16 * e ∧
      0 < 1 / 4 - R ^ 2 / a ^ 2 := by
    have hR0 : 0 < R := by linarith only [hR.1]
    have hl : (1 / 25 : ℝ) < R ^ 2 := by
      have hs := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) hR0.le).mpr hR.1
      nlinarith only [hs]
    have hu : R ^ 2 < (25 / 16 : ℝ) := by
      have hs := (sq_lt_sq₀ hR0.le (by norm_num : (0 : ℝ) ≤ 5 / 4)).mpr hR.2
      nlinarith only [hs]
    have hl' := mul_lt_mul_of_pos_right hl he
    have hu' := mul_lt_mul_of_pos_right hu he
    simp only [hdiv]
    refine ⟨by nlinarith only [hl'], hu', ?_⟩
    nlinarith only [hu', heSmall]
  have htheta (h R : ℝ) (hh : h ∈ I) (hR : R ∈ J) :
      0 < theta h R ∧ theta h R < Real.pi / 2 ∧
      Real.cos (theta h R) = Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h ∧
      ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => theta z.2 z.1) (R, h) := by
    have hrh := hr h hh
    have hs := hscale R hR
    have hp : 0 < Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h :=
      div_pos (Real.sqrt_pos.mpr hs.2.2) hrh.1
    have hl : Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h < 1 := by
      rw [div_lt_one hrh.1]
      change Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) < Real.sqrt (1 / 4 + h)
      apply Real.sqrt_lt_sqrt hs.2.2.le
      nlinarith only [(hI h hh).1, hs.1, he]
    refine ⟨Real.arccos_pos.mpr hl, Real.arccos_lt_pi_div_two.mpr hp,
      Real.cos_arccos (by linarith only [hp]) hl.le, ?_⟩
    apply (Real.contDiffAt_arccos (by linarith only [hp])
      (by linarith only [hl])).comp (R, h)
    have hrd := hrh.2.2.comp (R, h) (contDiffAt_snd (𝕜 := ℝ) (n := ∞))
    exact ((contDiffAt_const.sub ((contDiffAt_fst.pow 2).div_const (a ^ 2))).sqrt
      hs.2.2.ne').div hrd hrh.1.ne'
  have htd (R h : ℝ) (hR : R ∈ J) (hh : h ∈ I) :
      ContDiffAt ℝ ∞ (fun x => theta x R) h :=
    (htheta h R hh hR).2.2.2.comp h (contDiffAt_const.prodMk contDiffAt_id)
  have hmono (h : ℝ) (hh : h ∈ I) : StrictMonoOn (theta h) J := by
    intro R hR S hS hRS
    have hR0 : 0 < R := by linarith only [hR.1]
    have hS0 : 0 < S := by linarith only [hS.1]
    have hs : R ^ 2 < S ^ 2 := (sq_lt_sq₀ hR0.le hS0.le).mpr hRS
    have hd : R ^ 2 / a ^ 2 < S ^ 2 / a ^ 2 := div_lt_div_of_pos_right hs ha2
    have hroot := Real.sqrt_lt_sqrt (hscale S hS).2.2.le
      (by linarith only [hd] : 1 / 4 - S ^ 2 / a ^ 2 < 1 / 4 - R ^ 2 / a ^ 2)
    have hratio := div_lt_div_of_pos_right hroot (hr h hh).1
    exact Real.arccos_lt_arccos
      (by
        have hn := div_nonneg (Real.sqrt_nonneg (1 / 4 - S ^ 2 / a ^ 2))
          (hr h hh).1.le
        linarith only [hn])
      hratio (Real.arccos_pos.mp (htheta h R hh hR).1).le
  have hA (h : ℝ) (hh : h ∈ I) : 0 < A h := by
    dsimp only [A]
    linarith only [(htheta h 1 hh hj1).2.1, Real.pi_pos]
  have hAd (h : ℝ) (hh : h ∈ I) : ContDiffAt ℝ ∞ A h :=
    contDiffAt_const.sub (contDiffAt_const.mul (htd 1 h hj1 hh))
  have hphid (z : ℝ × ℝ) (hz : z.2 ∈ I) : ContDiffAt ℝ ∞ phi z :=
    ((htd 1 z.2 hj1 hz).comp z contDiffAt_snd).add
      (((hAd z.2 hz).comp z contDiffAt_snd).mul contDiffAt_fst)
  have hUopen : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hc := (htd (1 / 4) z.2 hj4 hz.1).comp z contDiffAt_snd
    have hp := hphid z hz.1
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds hz.1),
      hc.continuousAt.eventually_lt hp.continuousAt hz.2.1,
      hp.continuousAt.eventually_lt (continuousAt_const.sub hc.continuousAt)
        hz.2.2] with y hy hl hu
    exact ⟨hy, hl, hu⟩
  have h01 (h : ℝ) (hh : h ∈ I) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (t, h) ∈ U := by
    have hstrict := hmono h hh hj4 hj1 (by norm_num)
    have hl : 0 ≤ A h * t := mul_nonneg (hA h hh).le ht.1
    have hu : A h * t ≤ A h := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (hA h hh).le
    have heq : A h = 2 * Real.pi - 2 * theta h 1 := rfl
    exact ⟨hh, by dsimp only [phi]; linarith only [hstrict, hl],
      by dsimp only [phi]; linarith only [hstrict, hu, heq]⟩
  have hphiEnds (h R : ℝ) (hh : h ∈ I) :
      phi (tR h R, h) = theta h R ∧
      phi (1 - tR h R, h) = 2 * Real.pi - theta h R := by
    constructor <;> dsimp only [phi, tR]
    · field_simp [(hA h hh).ne']
      ring
    · field_simp [(hA h hh).ne']
      dsimp only [A]
      ring
  have hEnds (R h : ℝ) (hR : R ∈ Ioo (7 / 8 : ℝ) (9 / 8)) (hh : h ∈ I) :
      (tR h R, h) ∈ U ∧ (1 - tR h R, h) ∈ U := by
    have hstrict := hmono h hh hj4 (hRj R hR) (by linarith only [hR.1])
    have ht := htheta h R hh (hRj R hR)
    have ht4 := htheta h (1 / 4) hh hj4
    have hp := hphiEnds h R hh
    constructor
    · exact ⟨hh, by rw [hp.1]; exact hstrict,
        by rw [hp.1]; linarith only [ht.2.1, ht4.2.1, Real.pi_pos]⟩
    · exact ⟨hh, by rw [hp.2]; linarith only [ht.2.1, ht4.2.1, Real.pi_pos],
        by rw [hp.2]; linarith only [hstrict]⟩
  have htRd (z : ℝ × ℝ) (hR : z.1 ∈ J) (hh : z.2 ∈ I) :
      ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => tR p.2 p.1) z :=
    ((htheta z.2 z.1 hh hR).2.2.2.sub
      ((htd 1 z.2 hj1 hh).comp z contDiffAt_snd)).div
      ((hAd z.2 hh).comp z contDiffAt_snd) (hA z.2 hh).ne'
  have hDmem (z : ℝ × ℝ) (hz : z ∈ D) :
      z.1 ∈ Ioo (7 / 8 : ℝ) (9 / 8) ∧ z.2 ∈ I :=
    ⟨⟨by linarith only [hz.1.1], by linarith only [hz.1.2]⟩, h3 z.2 hz.2⟩
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  have hKcompact : IsCompact K0 := by
    refine ((isCompact_Icc.prod isCompact_Icc).union
      (hD.image_of_continuousOn ?_)).union (hD.image_of_continuousOn ?_)
    · intro z hz
      exact ((htRd z (hRj z.1 (hDmem z hz).1) (hDmem z hz).2).prodMk
        contDiffAt_snd).continuousAt.continuousWithinAt
    · intro z hz
      exact ((contDiffAt_const.sub (htRd z (hRj z.1 (hDmem z hz).1)
        (hDmem z hz).2)).prodMk contDiffAt_snd).continuousAt.continuousWithinAt
  have hKU : K0 ⊆ U := by
    intro z hz
    rcases hz with (hz | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact h01 z.2 (h3 z.2 hz.2) z.1 hz.1
    · exact (hEnds p.1 p.2 (hDmem p hp).1 (hDmem p hp).2).1
    · exact (hEnds p.1 p.2 (hDmem p hp).1 (hDmem p hp).2).2
  obtain ⟨chi, hchi, _, hchiSupp, hchiNear, _⟩ :=
    exists_compact_smooth_cutoff (K := Icc (3 / 4 : ℝ) 1)
      (U := Ioo (1 / 2 : ℝ) 2) isCompact_Icc isOpen_Ioo
      (by intro x hx; exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩)
  have hchiOne (x : ℝ) (hx : x ∈ Icc (3 / 4 : ℝ) 1) : chi x = 1 :=
    (eventually_nhdsSet_iff_forall.mp hchiNear x hx).self_of_nhds
  have hchiZero (x : ℝ) (hx : x < 1 / 2) : chi x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hxS
    linarith only [(hchiSupp hxS).1, hx]
  let v : (ℝ × ℝ) → ℝ := fun z => chi (Real.cos (phi z)) / A z.2 *
    (Real.cos (phi z) / (2 * (r z.2) ^ 2 * Real.sin (phi z)) -
      deriv (fun h => theta h 1) z.2 - deriv A z.2 * z.1)
  have htheta1On : ContDiffOn ℝ ∞ (fun h => theta h 1) I :=
    fun h hh => (htd 1 h hj1 hh).contDiffWithinAt
  have hAon : ContDiffOn ℝ ∞ A I := fun h hh => (hAd h hh).contDiffWithinAt
  have hBdiff : ContDiffOn ℝ ∞ (deriv (fun h => theta h 1)) I :=
    htheta1On.deriv_of_isOpen isOpen_Ioo (by simp)
  have hCdiff : ContDiffOn ℝ ∞ (deriv A) I :=
    hAon.deriv_of_isOpen isOpen_Ioo (by simp)
  have hv : ContDiffOn ℝ ∞ v U := by
    intro z hz
    have hp := hphid z hz.1
    by_cases hs : Real.sin (phi z) = 0
    · have hwindow : 0 < phi z ∧ phi z < 2 * Real.pi := by
        have ht := (htheta z.2 (1 / 4) hz.1 hj4).1
        exact ⟨by linarith only [ht, hz.2.1], by linarith only [ht, hz.2.2]⟩
      have hc : Real.cos (phi z) = -1 := by
        rcases Real.sin_eq_zero_iff_cos_eq.mp hs with hc | hc
        · have hz0 := (Real.cos_eq_one_iff_of_lt_of_lt
            (by linarith only [hwindow.1, Real.pi_pos]) hwindow.2).mp hc
          linarith only [hwindow.1, hz0]
        · exact hc
      have heq : v =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [hp.cos.continuousAt.eventually_lt continuousAt_const
          (by rw [hc]; norm_num : Real.cos (phi z) < (1 / 2 : ℝ))] with w hw
        simp only [v, hchiZero _ hw, zero_div, zero_mul]
      exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
    · have hrz := (hr z.2 hz.1).2.2.comp z contDiffAt_snd
      have hAz := (hAd z.2 hz.1).comp z contDiffAt_snd
      have hBz := (hBdiff.contDiffAt (isOpen_Ioo.mem_nhds hz.1)).comp z contDiffAt_snd
      have hCz := (hCdiff.contDiffAt (isOpen_Ioo.mem_nhds hz.1)).comp z contDiffAt_snd
      exact (((hchi.contDiffAt.comp z hp.cos).div hAz (hA z.2 hz.1).ne').mul
        (((hp.cos.div ((contDiffAt_const.mul (hrz.pow 2)).mul hp.sin)
          (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (hr z.2 hz.1).1.ne')) hs)).sub
            hBz).sub (hCz.mul contDiffAt_fst))).contDiffWithinAt
  have hthetaDeriv (R h : ℝ) (hR : R ∈ J) (hh : h ∈ I) :
      deriv (fun x => theta x R) h =
        Real.cos (theta h R) / (2 * (r h) ^ 2 * Real.sin (theta h R)) := by
    have ht := htheta h R hh hR
    have hs : 0 < Real.sin (theta h R) := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith only [ht.2.1, Real.pi_pos])
    have hrh := hr h hh
    have hrd : HasDerivAt r (1 / (2 * r h)) h :=
      ((hasDerivAt_id h).const_add (1 / 4)).sqrt (by
        change 1 / 4 + h ≠ 0
        nlinarith only [hrh.2.1, sq_pos_of_pos hrh.1])
    have htd' := ((htd R h hR hh).differentiableAt (by simp)).hasDerivAt
    have hprod := hrd.mul htd'.cos
    have hzero : HasDerivAt (fun x => r x * Real.cos (theta x R)) 0 h := by
      apply (hasDerivAt_const h (Real.sqrt (1 / 4 - R ^ 2 / a ^ 2))).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hh] with x hx
      rw [(htheta x R hx hR).2.2.1]
      field_simp [(hr x hx).1.ne']
    have heq := hprod.unique hzero
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 hrh.1.ne')) hs.ne')).mpr
    field_simp [hrh.1.ne'] at heq
    nlinarith only [heq]
  have hAderiv (h : ℝ) (hh : h ∈ I) :
      deriv A h = -(2 * deriv (fun x => theta x 1) h) := by
    have hh' := ((htd 1 h hj1 hh).differentiableAt (by simp)).hasDerivAt
    exact ((hh'.const_mul 2).const_sub (2 * Real.pi)).deriv
  have hCosPlateau (R h : ℝ) (hR : R ∈ Ioo (7 / 8 : ℝ) (9 / 8)) (hh : h ∈ I) :
      Real.cos (theta h R) ∈ Icc (3 / 4 : ℝ) 1 := by
    have hrh := hr h hh
    have hRhi : R ^ 2 < (81 / 64 : ℝ) := by
      have hR0 : 0 ≤ R := by linarith only [hR.1]
      have hh' := (sq_lt_sq₀ hR0 (by norm_num : (0 : ℝ) ≤ 9 / 8)).mpr hR.2
      nlinarith only [hh']
    have hRq : R ^ 2 / a ^ 2 < 81 / 64 * e := by
      rw [hdiv]
      exact mul_lt_mul_of_pos_right hRhi he
    have hroot : 3 / 4 * r h < Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) := by
      apply (Real.lt_sqrt (mul_nonneg (by norm_num) hrh.1.le)).mpr
      nlinarith only [hrh.2.1, (hI h hh).2, heSmall, hRq]
    refine ⟨?_, Real.cos_le_one _⟩
    rw [(htheta h R hh (hRj R hR)).2.2.1]
    exact ((lt_div_iff₀ hrh.1).mpr hroot).le
  have hTracks (R h : ℝ) (hR : R ∈ Ioo (7 / 8 : ℝ) (9 / 8)) (hh : h ∈ I) :
      HasDerivAt (fun x : ℝ => (tR x R, x)) (v (tR h R, h), 1) h ∧
      HasDerivAt (fun x : ℝ => (1 - tR x R, x)) (v (1 - tR h R, h), 1) h := by
    let dR : ℝ := deriv (fun x => theta x R) h
    let d1 : ℝ := deriv (fun x => theta x 1) h
    let dA : ℝ := deriv A h
    let dt : ℝ := ((dR - d1) * A h - (theta h R - theta h 1) * dA) / (A h) ^ 2
    have hdR : HasDerivAt (fun x => theta x R) dR h :=
      ((htd R h (hRj R hR) hh).differentiableAt (by simp)).hasDerivAt
    have hd1 : HasDerivAt (fun x => theta x 1) d1 h :=
      ((htd 1 h hj1 hh).differentiableAt (by simp)).hasDerivAt
    have hdA : HasDerivAt A dA h :=
      ((hAd h hh).differentiableAt (by simp)).hasDerivAt
    have hdt : HasDerivAt (fun x => tR x R) dt h :=
      (hdR.sub hd1).div hdA (hA h hh).ne'
    have hp := hphiEnds h R hh
    have hchiR := hchiOne _ (hCosPlateau R h hR hh)
    have hRform : Real.cos (theta h R) /
        (2 * (r h) ^ 2 * Real.sin (theta h R)) = dR :=
      (hthetaDeriv R h (hRj R hR) hh).symm
    have hAform : dA = -(2 * d1) := hAderiv h hh
    have hleft : v (tR h R, h) = dt := by
      dsimp only [v]
      rw [hp.1, hchiR, hRform]
      change 1 / A h * (dR - d1 - dA * tR h R) = dt
      dsimp only [tR, dt]
      field_simp [(hA h hh).ne']
    have hright : v (1 - tR h R, h) = -dt := by
      dsimp only [v]
      rw [hp.2, Real.cos_two_pi_sub, Real.sin_two_pi_sub, hchiR,
        mul_neg, div_neg, hRform]
      change 1 / A h * (-dR - d1 - dA * (1 - tR h R)) = -dt
      dsimp only [tR, dt]
      rw [hAform]
      field_simp [(hA h hh).ne']
      ring
    constructor
    · rw [hleft]
      exact hdt.prodMk (hasDerivAt_id h)
    · rw [hright]
      exact (hdt.const_sub 1).prodMk (hasDerivAt_id h)
  have hvEnds (h : ℝ) (hh : h ∈ I) : v (0, h) = 0 ∧ v (1, h) = 0 := by
    have ht := hTracks 1 h (by norm_num) hh
    have hleft : HasDerivAt (fun x : ℝ => ((0 : ℝ), x)) (v (0, h), 1) h := by
      simpa only [tR, sub_self, zero_div] using ht.1
    have hright : HasDerivAt (fun x : ℝ => ((1 : ℝ), x)) (v (1, h), 1) h := by
      simpa only [tR, sub_self, zero_div, sub_zero] using ht.2
    exact ⟨congrArg Prod.fst
      (hleft.unique ((hasDerivAt_const h (0 : ℝ)).prodMk (hasDerivAt_id h))),
      congrArg Prod.fst
        (hright.unique ((hasDerivAt_const h (1 : ℝ)).prodMk (hasDerivAt_id h)))⟩
  refine ⟨hUopen, hKcompact, hKU, v, hv, h01, hvEnds, ?_⟩
  intro R hR h hh
  exact ⟨(hEnds R h hR hh).1, (hEnds R h hR hh).2,
    (hTracks R h hR hh).1, (hTracks R h hR hh).2⟩

end PoincareConjecture.M25.Topology3D
