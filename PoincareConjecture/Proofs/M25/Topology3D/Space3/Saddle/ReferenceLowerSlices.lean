import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceMeridian
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialSphereChart
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 3000000 in

theorem exists_nonnested_reference_lower_slices
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2) :
    let L : OpenPartialHomeomorph ℝ ℝ := Classical.choose
      (Classical.choose_spec (Classical.choose_spec
        (exists_nonnested_reference_meridian sigma hsigma hsigmaSmall
          d hd hdNear hdZero hdBounds hdDeriv)))
    let eps : Fin 2 → ℝ := ![1, -1]
    let I : Set ℝ := Ioo (-1 / 4 : ℝ) 0
    let r : ℝ → ℝ := fun h => Real.sqrt (h + 1 / 4)
    let w : E2 × ℝ → ℝ := fun p => L.symm (r p.2 * (J2 p.1).2)
    let energy : E2 × ℝ → ℝ := fun p =>
      1 - (r p.2 * (J2 p.1).1) ^ 2 - (w p) ^ 2
    let U : Set (E2 × ℝ) := {p | p.2 ∈ I ∧
      r p.2 * (J2 p.1).2 ∈ Ioo (-1 / 2 : ℝ) (1 / 2) ∧ 0 < energy p}
    let V : Fin 2 → Set (E2 × ℝ) := fun i =>
      {p | p.2 ∈ I ∧ 0 < eps i * (J2 p.1).2 ∧ 2 * ‖p.1‖ ^ 2 < 1}
    let B0 := nonnestedReferenceBallChart 0 d hd
    let f : UnitTwoSphere → ℝ := fun p =>
      1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
        d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
    ∃ T : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ),
      (∀ i : Fin 2,
        (T i).source = U ∧ (T i).target = V i ∧
        ContDiffOn ℝ ∞ (T i) U ∧ ContDiffOn ℝ ∞ (T i).symm (V i) ∧
        (∀ p ∈ U, T i p =
          (J2.symm (r p.2 * (J2 p.1).1 / Real.sqrt 2,
            eps i * Real.sqrt (energy p) / Real.sqrt 2), p.2)) ∧
        (∀ p ∈ V i, (T i).symm p =
          (J2.symm (Real.sqrt 2 * (J2 p.1).1 / r p.2,
            L (-Real.sqrt (1 - 2 * ‖p.1‖ ^ 2)) / r p.2), p.2))) ∧
      closedBall (0 : E2) 1 ×ˢ I ⊆ U ∧
      (∀ h ∈ I, ∃ B : Fin 2 → BallNeighborhoodChart E2 E2,
        (∀ i : Fin 2,
          (B i).chart.source = {x : E2 | (x, h) ∈ U} ∧
          (B i).chart.target =
            {y : E2 | 0 < eps i * (J2 y).2 ∧ 2 * ‖y‖ ^ 2 < 1} ∧
          (∀ x : E2, (B i).chart x = (T i (x, h)).1) ∧
          (∀ y : E2, (B i).chart.symm y = ((T i).symm (y, h)).1) ∧
          (B i).closedRegion ⊆ {y : E2 | 0 < eps i * (J2 y).2}) ∧
        Disjoint (B 0).closedRegion (B 1).closedRegion ∧
        (⋃ i : Fin 2, (B i).inside) = {y : E2 | (J2 y, h) ∈ B0.inside} ∧
        (⋃ i : Fin 2, (B i).closedRegion) =
          {y : E2 | (J2 y, h) ∈ B0.closedRegion} ∧
        (⋃ i : Fin 2, (B i).boundary) =
          {y : E2 | (J2 y, h) ∈ B0.boundary}) ∧
      ∀ p : UnitTwoSphere, f p ∈ I →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0 := by
  classical
  let hm := exists_nonnested_reference_meridian sigma hsigma hsigmaSmall
    d hd hdNear hdZero hdBounds hdDeriv
  let e := Classical.choose hm
  let ell := Classical.choose (Classical.choose_spec hm)
  let L := Classical.choose (Classical.choose_spec (Classical.choose_spec hm))
  obtain ⟨he, _, hell, hLs, hLt, hLsm, hLism, hLmono, _, _, _,
    hLm, _, hLz, _, hLsq⟩ :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hm))
  change 0 < e at he
  change ell < -1 / 2 at hell
  change L.source = Ioo (-1 - e) (1 / 4) at hLs
  change L.target = Ioo ell (3 / 4) at hLt
  change ContDiffOn ℝ ∞ L L.source at hLsm
  change ContDiffOn ℝ ∞ L.symm L.target at hLism
  change StrictMonoOn L L.source at hLmono
  change L (-1) = -1 / 2 at hLm
  change L 0 = 1 / 2 at hLz
  change ∀ t ∈ L.source, (L t) ^ 2 = t ^ 2 + t + d (1 - t ^ 2) + 1 / 4 at hLsq
  let eps : Fin 2 → ℝ := ![1, -1]
  let I : Set ℝ := Ioo (-1 / 4 : ℝ) 0
  let r : ℝ → ℝ := fun h => Real.sqrt (h + 1 / 4)
  let X : E2 → ℝ := fun x => (J2 x).1
  let Y : E2 → ℝ := fun x => (J2 x).2
  let w : E2 × ℝ → ℝ := fun p => L.symm (r p.2 * Y p.1)
  let energy : E2 × ℝ → ℝ := fun p => 1 - (r p.2 * X p.1) ^ 2 - (w p) ^ 2
  let U0 : Set (E2 × ℝ) := {p | p.2 ∈ I ∧ r p.2 * Y p.1 ∈ Ioo (-1 / 2 : ℝ) (1 / 2)}
  let U : Set (E2 × ℝ) := {p | p.2 ∈ I ∧
    r p.2 * Y p.1 ∈ Ioo (-1 / 2 : ℝ) (1 / 2) ∧ 0 < energy p}
  let V : Fin 2 → Set (E2 × ℝ) := fun i =>
    {p | p.2 ∈ I ∧ 0 < eps i * Y p.1 ∧ 2 * ‖p.1‖ ^ 2 < 1}
  let a : ℝ := Real.sqrt 2
  let q : E2 → ℝ := fun y => 2 * ‖y‖ ^ 2
  let s : E2 → ℝ := fun y => -Real.sqrt (1 - q y)
  let lo : E2 → ℝ := fun y => 1 - 2 * (Y y) ^ 2 + d (q y) + s y
  let N : E2 → ℝ → ℝ := fun y h => q y + (h - 1 + 2 * (Y y) ^ 2 - d (q y)) ^ 2
  let B0 := nonnestedReferenceBallChart 0 d hd
  let f : UnitTwoSphere → ℝ := fun p =>
    1 + (p : E3) 2 - ((p : E3) 1) ^ 2 + d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : a ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have heps (i : Fin 2) : (eps i) ^ 2 = 1 ∧ eps i * eps i = 1 := by
    fin_cases i <;> norm_num [eps]
  have hepsSq (i : Fin 2) (t : ℝ) : (eps i * t) ^ 2 = t ^ 2 := by
    rw [mul_pow, (heps i).1, one_mul]
  have hXY (x : E2) : (X x) ^ 2 + (Y x) ^ 2 = ‖x‖ ^ 2 := hJ2 x
  have hq (y : E2) : q y = 2 * ((X y) ^ 2 + (Y y) ^ 2) := by rw [hXY]
  have hnorm (u v : ℝ) : ‖J2.symm (u, v)‖ ^ 2 = u ^ 2 + v ^ 2 := by
    simpa only [J2.apply_symm_apply] using (hJ2 (J2.symm (u, v))).symm
  have hX : ContDiff ℝ ∞ X := J2.contDiff.fst
  have hY : ContDiff ℝ ∞ Y := J2.contDiff.snd
  have hmemL (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 0) : t ∈ L.source := by
    rw [hLs]; constructor <;> linarith [ht.1, ht.2]
  have hmL : (-1 : ℝ) ∈ L.source := by rw [hLs]; constructor <;> linarith
  have hzL : (0 : ℝ) ∈ L.source := by rw [hLs]; constructor <;> linarith
  have hhalfL (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 0) :
      L t ∈ Ioo (-1 / 2 : ℝ) (1 / 2) := by
    have hm := hLmono hmL (hmemL t ht) ht.1
    have hz := hLmono (hmemL t ht) hzL ht.2
    rw [hLm] at hm; rw [hLz] at hz
    exact ⟨hm, hz⟩
  have htL (z : ℝ) (hz : z ∈ Ioo (-1 / 2 : ℝ) (1 / 2)) : z ∈ L.target := by
    rw [hLt]; constructor <;> linarith [hz.1, hz.2]
  have hinvL (z : ℝ) (hz : z ∈ Ioo (-1 / 2 : ℝ) (1 / 2)) :
      L.symm z ∈ Ioo (-1 : ℝ) 0 ∧ L (L.symm z) = z := by
    have ht := htL z hz
    have hs := L.map_target ht
    have heq := L.right_inv ht
    refine ⟨⟨?_, ?_⟩, heq⟩
    · by_contra hh
      have hle := hLmono.monotoneOn hs hmL (le_of_not_gt hh)
      rw [hLm, heq] at hle
      linarith [hz.1]
    · by_contra hh
      have hle := hLmono.monotoneOn hzL hs (le_of_not_gt hh)
      rw [hLz, heq] at hle
      linarith [hz.2]
  have hr (h : ℝ) (hh : h ∈ I) : 0 < r h ∧ (r h) ^ 2 = h + 1 / 4 ∧ r h < 1 / 2 := by
    have hp : 0 < h + 1 / 4 := by linarith [hh.1]
    have hs : (r h) ^ 2 = h + 1 / 4 := Real.sq_sqrt hp.le
    have hr0 : 0 < r h := Real.sqrt_pos.mpr hp
    refine ⟨hr0, hs, ?_⟩
    apply (sq_lt_sq₀ hr0.le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
    nlinarith [hh.2]
  have hsRange (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ V i) :
      s p.1 ∈ Ioo (-1 : ℝ) 0 ∧ (s p.1) ^ 2 = 1 - q p.1 := by
    have hy : Y p.1 ≠ 0 := by
      intro hy
      have hpY : 0 < eps i * Y p.1 := hp.2.1
      rw [hy, mul_zero] at hpY
      exact lt_irrefl _ hpY
    have hq0 : 0 < q p.1 := by rw [hq]; nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (X p.1)]
    have hq1 : q p.1 < 1 := hp.2.2
    have hs2 : (s p.1) ^ 2 = 1 - q p.1 := by
      dsimp only [s]; rw [neg_sq, Real.sq_sqrt (by linarith)]
    have hs0 : s p.1 < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr (by linarith))
    exact ⟨⟨by nlinarith [hs2, sq_nonneg (s p.1 + 1)], hs0⟩, hs2⟩
  let F : Fin 2 → E2 × ℝ → E2 × ℝ := fun i p =>
    (J2.symm (r p.2 * X p.1 / a, eps i * Real.sqrt (energy p) / a), p.2)
  let G : E2 × ℝ → E2 × ℝ := fun p =>
    (J2.symm (a * X p.1 / r p.2, L (s p.1) / r p.2), p.2)
  have hFc (i : Fin 2) (p : E2 × ℝ) :
      X (F i p).1 = r p.2 * X p.1 / a ∧
      Y (F i p).1 = eps i * Real.sqrt (energy p) / a := by simp [F, X, Y]
  have hGc (p : E2 × ℝ) : X (G p).1 = a * X p.1 / r p.2 ∧
      Y (G p).1 = L (s p.1) / r p.2 := by simp [G, X, Y]
  have hqF (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ U) :
      q (F i p).1 = 1 - (w p) ^ 2 := by
    rw [hq, (hFc i p).1, (hFc i p).2]
    simp only [div_pow, hepsSq, ha2, Real.sq_sqrt hp.2.2.le]
    dsimp only [energy]; ring
  have hFmap (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ U) : F i p ∈ V i := by
    have hw := (hinvL (r p.2 * Y p.1) hp.2.1).1
    refine ⟨hp.1, ?_, ?_⟩
    · rw [(hFc i p).2, ← mul_div_assoc, ← mul_assoc, (heps i).2, one_mul]
      exact div_pos (Real.sqrt_pos.mpr hp.2.2) ha
    · change q (F i p).1 < 1
      rw [hqF i p hp]
      change -1 < w p ∧ w p < 0 at hw
      nlinarith [sq_pos_of_ne_zero hw.2.ne]
  have hsF (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ U) : s (F i p).1 = w p := by
    have hw := (hinvL (r p.2 * Y p.1) hp.2.1).1.2
    change w p < 0 at hw
    dsimp only [s]
    rw [hqF i p hp, show 1 - (1 - (w p) ^ 2) = (w p) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_neg hw, neg_neg]
  have hGF (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ U) : G (F i p) = p := by
    have hri := (hr p.2 hp.1).1.ne'
    have hw := (hinvL (r p.2 * Y p.1) hp.2.1).2
    change L (w p) = r p.2 * Y p.1 at hw
    apply Prod.ext
    · apply J2.injective
      simp only [G, J2.apply_symm_apply]
      apply Prod.ext
      · change a * X (F i p).1 / r p.2 = X p.1
        rw [(hFc i p).1]; field_simp [ha.ne', hri]
      · change L (s (F i p).1) / r p.2 = Y p.1
        rw [hsF i p hp, hw]; field_simp [hri]
    · rfl
  have hGdata (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ V i) :
      r p.2 * Y (G p).1 = L (s p.1) ∧ w (G p) = s p.1 ∧
      energy (G p) = (a * Y p.1) ^ 2 := by
    have hri := (hr p.2 hp.1).1.ne'
    have hs := hsRange i p hp
    have harg : r p.2 * Y (G p).1 = L (s p.1) := by
      rw [(hGc p).2]; field_simp [hri]
    have hw : w (G p) = s p.1 := by
      change L.symm (r p.2 * Y (G p).1) = s p.1
      rw [harg]; exact L.left_inv (hmemL _ hs.1)
    refine ⟨harg, hw, ?_⟩
    change 1 - (r p.2 * X (G p).1) ^ 2 - (w (G p)) ^ 2 = _
    rw [(hGc p).1, hw, mul_div_cancel₀ _ hri, hs.2, hq]
    simp only [mul_pow, ha2]; ring
  have hGmap (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ V i) : G p ∈ U := by
    have hs := hsRange i p hp
    have hg := hGdata i p hp
    refine ⟨hp.1, ?_, ?_⟩
    · change r p.2 * Y (G p).1 ∈ Ioo (-1 / 2 : ℝ) (1 / 2)
      rw [hg.1]; exact hhalfL _ hs.1
    · rw [hg.2.2]
      have hy : Y p.1 ≠ 0 := by
        intro hy
        have hpY : 0 < eps i * Y p.1 := hp.2.1
        rw [hy, mul_zero] at hpY
        exact lt_irrefl _ hpY
      exact sq_pos_of_ne_zero (mul_ne_zero ha.ne' hy)
  have hFG (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ V i) : F i (G p) = p := by
    have hri := (hr p.2 hp.1).1.ne'
    have hg := hGdata i p hp
    have hpE := (hGmap i p hp).2.2
    have hpos : 0 < eps i * (a * Y p.1) := by
      simpa only [mul_left_comm] using mul_pos ha hp.2.1
    have hroot : Real.sqrt (energy (G p)) = eps i * (a * Y p.1) := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hpos.le).mp
      rw [Real.sq_sqrt hpE.le, hg.2.2, hepsSq]
    apply Prod.ext
    · apply J2.injective
      simp only [F, J2.apply_symm_apply]
      apply Prod.ext
      · change r p.2 * X (G p).1 / a = X p.1
        rw [(hGc p).1]; field_simp [hri, ha.ne']
      · change eps i * Real.sqrt (energy (G p)) / a = Y p.1
        rw [hroot, ← mul_assoc, (heps i).2, one_mul]; field_simp [ha.ne']
    · rfl
  have hrsm : ContDiffOn ℝ ∞ r I :=
    (contDiff_id.add contDiff_const).contDiffOn.sqrt (fun h hh => by
      change h + 1 / 4 ≠ 0
      linarith [hh.1])
  have hrc : Continuous r := (continuous_id.add continuous_const).sqrt
  have hU0 : IsOpen U0 := (isOpen_Ioo.preimage continuous_snd).inter
    (isOpen_Ioo.preimage ((hrc.comp continuous_snd).mul (hY.continuous.comp continuous_fst)))
  have hru : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => r p.2) U0 :=
    hrsm.comp contDiff_snd.contDiffOn (fun _ hp => hp.1)
  have hXu : ContDiff ℝ ∞ (fun p : E2 × ℝ => X p.1) := hX.comp contDiff_fst
  have hYu : ContDiff ℝ ∞ (fun p : E2 × ℝ => Y p.1) := hY.comp contDiff_fst
  have hwsm : ContDiffOn ℝ ∞ w U0 := hLism.comp
    (hru.mul hYu.contDiffOn) (fun p hp => htL _ hp.2)
  have hesm : ContDiffOn ℝ ∞ energy U0 :=
    (contDiffOn_const.sub ((hru.mul hXu.contDiffOn).pow 2)).sub (hwsm.pow 2)
  have hUU0 : U ⊆ U0 := fun _ hp => ⟨hp.1, hp.2.1⟩
  have hU : IsOpen U := by
    have ho := hesm.continuousOn.isOpen_inter_preimage hU0 (isOpen_Ioi (a := (0 : ℝ)))
    have hset : U = U0 ∩ energy ⁻¹' Ioi 0 := by
      apply Set.ext
      intro p
      exact and_assoc.symm
    rw [hset]
    exact ho
  have hV (i : Fin 2) : IsOpen (V i) :=
    (isOpen_Ioo.preimage continuous_snd).inter
      ((isOpen_lt continuous_const (continuous_const.mul hYu.continuous)).inter
        (isOpen_lt (continuous_const.mul (continuous_fst.norm.pow 2)) continuous_const))
  have hFsm (i : Fin 2) : ContDiffOn ℝ ∞ (F i) U := by
    have he := (hesm.mono hUU0).sqrt (fun _ hp => hp.2.2.ne')
    exact (J2.symm.contDiff.comp_contDiffOn
      (((hru.mono hUU0).mul hXu.contDiffOn).div_const a |>.prodMk
        ((contDiffOn_const.mul he).div_const a))).prodMk contDiff_snd.contDiffOn
  have hGsm (i : Fin 2) : ContDiffOn ℝ ∞ G (V i) := by
    have hs : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => s p.1) (V i) :=
      ((contDiff_const.sub (contDiff_const.mul (contDiff_fst.norm_sq ℝ))).contDiffOn.sqrt
        (fun _ hp => by linarith [hp.2.2])).neg
    have hLs0 := hLsm.comp hs (fun p hp => hmemL _ (hsRange i p hp).1)
    have hr0 : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => r p.2) (V i) :=
      hrsm.comp contDiff_snd.contDiffOn (fun p hp => hp.1)
    exact (J2.symm.contDiff.comp_contDiffOn
      (((contDiffOn_const.mul hXu.contDiffOn).div hr0
        (fun p hp => (hr p.2 hp.1).1.ne')).prodMk
        (hLs0.div hr0 (fun p hp => (hr p.2 hp.1).1.ne')))).prodMk contDiff_snd.contDiffOn
  let T : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ) := fun i => {
    toFun := F i, invFun := G, source := U, target := V i
    map_source' := hFmap i, map_target' := hGmap i
    left_inv' := hGF i, right_inv' := hFG i
    open_source := hU, open_target := hV i
    continuousOn_toFun := (hFsm i).continuousOn
    continuousOn_invFun := (hGsm i).continuousOn }
  have hlower (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 0) : 0 ≤ 1 + t + d (1 - t ^ 2) := by
    have hq0 : 0 ≤ 1 - t ^ 2 := by
      nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t + 1)
        (by linarith [ht.2] : 0 ≤ 1 - t)]
    have hq1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    have hd0 := (hdBounds _ hq0).1
    have hp := mul_nonneg hq0 (sub_nonneg.mpr hq1)
    nlinarith [sq_nonneg (1 + t)]
  have hCylinder : closedBall (0 : E2) 1 ×ˢ I ⊆ U := by
    rintro ⟨x, h⟩ ⟨hx, hh⟩
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hy : -1 ≤ Y x ∧ Y x ≤ 1 := by
      constructor <;> nlinarith [hXY x, sq_nonneg (X x),
        sq_nonneg (Y x - 1), sq_nonneg (Y x + 1)]
    have hr0 := hr h hh
    have hz : r h * Y x ∈ Ioo (-1 / 2 : ℝ) (1 / 2) := by
      have h1 := mul_le_mul_of_nonneg_left hy.1 hr0.1.le
      have h2 := mul_le_mul_of_nonneg_left hy.2 hr0.1.le
      constructor <;> nlinarith
    have hw := hinvL (r h * Y x) hz
    change w (x, h) ∈ Ioo (-1 : ℝ) 0 ∧ L (w (x, h)) = r h * Y x at hw
    have hsq := hLsq (w (x, h)) (hmemL _ hw.1)
    have hnonneg := hlower (w (x, h)) ⟨hw.1.1.le, hw.1.2.le⟩
    have hsum : (r h * X x) ^ 2 + (L (w (x, h))) ^ 2 = (r h) ^ 2 * ‖x‖ ^ 2 := by
      rw [hw.2, ← hXY x]; ring
    have hle := mul_le_mul_of_nonneg_left hx2 (sq_nonneg (r h))
    refine ⟨hh, hz, ?_⟩
    change 0 < 1 - (r h * X x) ^ 2 - (w (x, h)) ^ 2
    nlinarith [hr0.2.1, hh.2]
  have hNative (y : E2) (h : ℝ) :
      ((J2 y, h) ∈ B0.inside ↔ N y h < 1) ∧
      ((J2 y, h) ∈ B0.closedRegion ↔ N y h ≤ 1) ∧
      ((J2 y, h) ∈ B0.boundary ↔ N y h = 1) := by
    simpa only [B0, N, q, X, Y, sub_zero, hJ2 y] using
      (nonnestedReferenceBallChart_regions 0 d hd).2.2 (J2 y, h)
  have hUpper (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
      0 < 1 - z + d z + Real.sqrt (1 - z) := by
    by_cases hzs : sigma ≤ z
    · rw [hdZero z hzs]; nlinarith [Real.sqrt_nonneg (1 - z)]
    · have hzsmall : z < 1 / 16 := lt_of_lt_of_le (lt_of_not_ge hzs) hsigmaSmall
      have hzsq : z ^ 2 ≤ 1 / 256 := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 16 - z)
          (by linarith : 0 ≤ 1 / 16 + z)]
      nlinarith [(hdBounds z hz0).1, Real.sqrt_nonneg (1 - z)]
  have hSlice (y : E2) (h : ℝ) (hq1 : q y < 1) (hh : h < 0) :
      (N y h < 1 ↔ lo y < h) ∧ (N y h ≤ 1 ↔ lo y ≤ h) ∧
      (N y h = 1 ↔ lo y = h) := by
    let b := 1 - 2 * (Y y) ^ 2 + d (q y) + Real.sqrt (1 - q y)
    have hq0 : 0 ≤ q y := by dsimp [q]; positivity
    have hup := hUpper (q y) hq0 hq1
    have hb : h - b < 0 := by
      have hqeq := hq y
      dsimp only [b]; nlinarith [sq_nonneg (X y)]
    have hs2 := Real.sq_sqrt (sub_pos.mpr hq1).le
    have hfactor : N y h - 1 = (h - lo y) * (h - b) := by
      dsimp [N, lo, s, b]; nlinarith only [hs2]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro hn; by_contra hl
        have hm := mul_nonneg_of_nonpos_of_nonpos (by linarith : h - lo y ≤ 0) hb.le
        nlinarith
      · intro hl
        have hm := mul_neg_of_pos_of_neg (sub_pos.mpr hl) hb
        nlinarith
    · constructor
      · intro hn; by_contra hl
        have hm := mul_pos_of_neg_of_neg (by linarith : h - lo y < 0) hb
        nlinarith
      · intro hl
        have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) hb.le
        nlinarith
    · constructor
      · intro hn
        have hm : (h - lo y) * (h - b) = 0 := by linarith
        have he := (mul_eq_zero.mp hm).resolve_right hb.ne
        linarith
      · intro hl; rw [hl, sub_self, zero_mul] at hfactor; linarith
  have hCover (y : E2) (h : ℝ) (hh : h ∈ I) (hn : N y h ≤ 1) :
      ∃ i : Fin 2, (y, h) ∈ V i := by
    have hq0 : 0 ≤ q y := by dsimp [q]; positivity
    have hqle : q y ≤ 1 := by
      dsimp only [N] at hn
      nlinarith [sq_nonneg (h - 1 + 2 * (Y y) ^ 2 - d (q y))]
    have hq1 : q y < 1 := by
      by_contra hhq
      have hqe : q y = 1 := le_antisymm hqle (le_of_not_gt hhq)
      have hd1 : d 1 = 0 := hdZero 1 (by linarith)
      dsimp only [N] at hn
      rw [hqe, hd1] at hn
      have hxy := hq y
      rw [hqe] at hxy
      have hz : h - 1 + 2 * (Y y) ^ 2 = 0 := by
        apply (sq_eq_zero_iff).mp
        nlinarith [sq_nonneg (h - 1 + 2 * (Y y) ^ 2)]
      nlinarith [sq_nonneg (X y), hh.2]
    have hlo := (hSlice y h hq1 hh.2).2.1.mp hn
    have hy : Y y ≠ 0 := by
      intro hy0
      have hs2 := Real.sq_sqrt (sub_pos.mpr hq1).le
      have hprod := mul_nonneg hq0 (sub_nonneg.mpr hqle)
      have hd0 := (hdBounds (q y) hq0).1
      have hs0 := Real.sqrt_nonneg (1 - q y)
      dsimp only [lo, s] at hlo
      rw [hy0] at hlo
      nlinarith [sq_nonneg (1 - Real.sqrt (1 - q y)), hh.2]
    by_cases hpos : 0 < Y y
    · exact ⟨0, hh, by simpa [eps] using hpos, hq1⟩
    · exact ⟨1, hh, by simpa [eps] using neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hy), hq1⟩
  have hLevel (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ V i) :
      (‖(G p).1‖ < 1 ↔ N p.1 p.2 < 1) ∧
      (‖(G p).1‖ ≤ 1 ↔ N p.1 p.2 ≤ 1) ∧
      (‖(G p).1‖ = 1 ↔ N p.1 p.2 = 1) := by
    have hs := hsRange i p hp
    have hr0 := hr p.2 hp.1
    have hls := hLsq (s p.1) (hmemL _ hs.1)
    have harg : 1 - (s p.1) ^ 2 = q p.1 := by linarith [hs.2]
    rw [harg] at hls
    have hgn : (r p.2) ^ 2 * ‖(G p).1‖ ^ 2 = (a * X p.1) ^ 2 + (L (s p.1)) ^ 2 := by
      change (r p.2) ^ 2 * ‖J2.symm (a * X p.1 / r p.2, L (s p.1) / r p.2)‖ ^ 2 = _
      rw [hnorm]; field_simp [hr0.1.ne']
    have heq : (r p.2) ^ 2 * (‖(G p).1‖ ^ 2 - 1) = lo p.1 - p.2 := by
      dsimp only [lo]
      rw [mul_pow, ha2] at hgn
      nlinarith [hq p.1, hs.2, hr0.2.1]
    have hscale : 0 < (r p.2) ^ 2 := sq_pos_of_pos hr0.1
    have hh := hSlice p.1 p.2 hp.2.2 hp.1.2
    refine ⟨?_, ?_, ?_⟩
    · calc
        ‖(G p).1‖ < 1 ↔ ‖(G p).1‖ ^ 2 < 1 := by
          constructor <;> intro ht <;> nlinarith only [ht, norm_nonneg (G p).1]
        _ ↔ (r p.2) ^ 2 * ‖(G p).1‖ ^ 2 < (r p.2) ^ 2 * 1 :=
          (mul_lt_mul_iff_right₀ hscale).symm
        _ ↔ lo p.1 < p.2 := by constructor <;> intro ht <;> nlinarith only [heq, ht]
        _ ↔ N p.1 p.2 < 1 := hh.1.symm
    · calc
        ‖(G p).1‖ ≤ 1 ↔ ‖(G p).1‖ ^ 2 ≤ 1 := by
          constructor <;> intro ht <;> nlinarith only [ht, norm_nonneg (G p).1]
        _ ↔ (r p.2) ^ 2 * ‖(G p).1‖ ^ 2 ≤ (r p.2) ^ 2 * 1 :=
          (mul_le_mul_iff_right₀ hscale).symm
        _ ↔ lo p.1 ≤ p.2 := by constructor <;> intro ht <;> nlinarith only [heq, ht]
        _ ↔ N p.1 p.2 ≤ 1 := hh.2.1.symm
    · calc
        ‖(G p).1‖ = 1 ↔ ‖(G p).1‖ ^ 2 = 1 := by
          constructor <;> intro ht <;> nlinarith only [ht, norm_nonneg (G p).1]
        _ ↔ (r p.2) ^ 2 * ‖(G p).1‖ ^ 2 = (r p.2) ^ 2 * 1 :=
          ⟨congrArg (fun t : ℝ => (r p.2) ^ 2 * t), mul_left_cancel₀ hscale.ne'⟩
        _ ↔ lo p.1 = p.2 := by constructor <;> intro ht <;> nlinarith only [heq, ht]
        _ ↔ N p.1 p.2 = 1 := hh.2.2.symm
  have hFibers (h : ℝ) (hh : h ∈ I) :
      ∃ B : Fin 2 → BallNeighborhoodChart E2 E2,
        (∀ i : Fin 2,
          (B i).chart.source = {x : E2 | (x, h) ∈ U} ∧
          (B i).chart.target = {y : E2 | 0 < eps i * Y y ∧ q y < 1} ∧
          (∀ x : E2, (B i).chart x = (T i (x, h)).1) ∧
          (∀ y : E2, (B i).chart.symm y = ((T i).symm (y, h)).1) ∧
          (B i).closedRegion ⊆ {y : E2 | 0 < eps i * Y y}) ∧
        Disjoint (B 0).closedRegion (B 1).closedRegion ∧
        (⋃ i : Fin 2, (B i).inside) = {y : E2 | (J2 y, h) ∈ B0.inside} ∧
        (⋃ i : Fin 2, (B i).closedRegion) = {y : E2 | (J2 y, h) ∈ B0.closedRegion} ∧
        (⋃ i : Fin 2, (B i).boundary) = {y : E2 | (J2 y, h) ∈ B0.boundary} := by
    let b : Fin 2 → OpenPartialHomeomorph E2 E2 := fun i => {
      toFun := fun x => (F i (x, h)).1
      invFun := fun y => (G (y, h)).1
      source := {x | (x, h) ∈ U}
      target := {y | 0 < eps i * Y y ∧ q y < 1}
      map_source' x hx := (hFmap i (x, h) hx).2
      map_target' y hy := hGmap i (y, h) ⟨hh, hy⟩
      left_inv' x hx := congrArg Prod.fst (hGF i (x, h) hx)
      right_inv' y hy := congrArg Prod.fst (hFG i (y, h) ⟨hh, hy⟩)
      open_source := hU.preimage (continuous_id.prodMk continuous_const)
      open_target := (isOpen_lt continuous_const (continuous_const.mul hY.continuous)).inter
        (isOpen_lt (continuous_const.mul (continuous_norm.pow 2)) continuous_const)
      continuousOn_toFun := ((hFsm i).comp
        (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => hx)).fst.continuousOn
      continuousOn_invFun := ((hGsm i).comp
        (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hy => ⟨hh, hy⟩)).fst.continuousOn }
    let B : Fin 2 → BallNeighborhoodChart E2 E2 := fun i => {
      chart := b i
      closedBall_subset_source := fun x hx => hCylinder ⟨hx, hh⟩
      smooth := ((hFsm i).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => hx)).fst
      smooth_symm := ((hGsm i).comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun _ hy => ⟨hh, hy⟩)).fst }
    have htarget (i : Fin 2) {y : E2} (hy : y ∈ (B i).closedRegion) : (y, h) ∈ V i := by
      obtain ⟨x, hx, rfl⟩ := hy
      exact hFmap i (x, h) (hCylinder ⟨hx, hh⟩)
    have himage (i : Fin 2) (y : E2) (hy : (y, h) ∈ V i)
        (S : Set E2) (hS : S ⊆ closedBall (0 : E2) 1) :
        y ∈ (B i).chart '' S ↔ (G (y, h)).1 ∈ S := by
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (B i).chart.symm ((B i).chart x) ∈ S
        rw [(B i).chart.left_inv ((B i).closedBall_subset_source (hS hx))]
        exact hx
      · intro hx
        exact ⟨(G (y, h)).1, hx, congrArg Prod.fst (hFG i (y, h) hy)⟩
    have htest (i : Fin 2) (y : E2) (hy : (y, h) ∈ V i) :
        (y ∈ (B i).inside ↔ (J2 y, h) ∈ B0.inside) ∧
        (y ∈ (B i).closedRegion ↔ (J2 y, h) ∈ B0.closedRegion) ∧
        (y ∈ (B i).boundary ↔ (J2 y, h) ∈ B0.boundary) := by
      have ht := hLevel i (y, h) hy
      have hn := hNative y h
      refine ⟨?_, ?_, ?_⟩
      · exact (himage i y hy _ ball_subset_closedBall).trans
          (mem_ball_zero_iff.trans (ht.1.trans hn.1.symm))
      · exact (himage i y hy _ (Subset.refl _)).trans
          (mem_closedBall_zero_iff.trans (ht.2.1.trans hn.2.1.symm))
      · exact (himage i y hy _ sphere_subset_closedBall).trans
          (mem_sphere_zero_iff_norm.trans (ht.2.2.trans hn.2.2.symm))
    have hinside (i : Fin 2) : (B i).inside ⊆ (B i).closedRegion :=
      image_mono ball_subset_closedBall
    have hboundary (i : Fin 2) : (B i).boundary ⊆ (B i).closedRegion :=
      image_mono sphere_subset_closedBall
    refine ⟨B, (fun i => ⟨rfl, rfl, fun _ => rfl, fun _ => rfl,
      fun _ hy => (htarget i hy).2.1⟩), ?_, ?_, ?_, ?_⟩
    · apply disjoint_left.mpr
      intro y h0 h1
      have h0' := (htarget 0 h0).2.1
      have h1' := (htarget 1 h1).2.1
      norm_num [eps] at h0' h1'
      linarith
    · ext y; constructor
      · intro hy; obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        exact (htest i y (htarget i (hinside i hi))).1.mp hi
      · intro hy
        obtain ⟨i, hi⟩ := hCover y h hh ((hNative y h).1.mp hy).le
        exact mem_iUnion.mpr ⟨i, (htest i y hi).1.mpr hy⟩
    · ext y; constructor
      · intro hy; obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        exact (htest i y (htarget i hi)).2.1.mp hi
      · intro hy
        obtain ⟨i, hi⟩ := hCover y h hh ((hNative y h).2.1.mp hy)
        exact mem_iUnion.mpr ⟨i, (htest i y hi).2.1.mpr hy⟩
    · ext y; constructor
      · intro hy; obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        exact (htest i y (htarget i (hboundary i hi))).2.2.mp hi
      · intro hy
        obtain ⟨i, hi⟩ := hCover y h hh ((hNative y h).2.2.mp hy).le
        exact mem_iUnion.mpr ⟨i, (htest i y hi).2.2.mpr hy⟩
  refine ⟨T, (fun i => ⟨rfl, rfl, hFsm i, hGsm i, fun _ _ => rfl, fun _ _ => rfl⟩),
    hCylinder, hFibers, ?_⟩
  intro p hp
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  change f p ∈ I at hp
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0
  let h0 := f p
  let y : E2 := J2.symm ((p : E3) 0 / a, (p : E3) 1 / a)
  have hyb : (J2 y, h0) ∈ B0.boundary := by
    refine ⟨(p : E3), p.property, ?_⟩
    change nonnestedReferenceDiffeomorph 0 d hd (p : E3) = (J2 y, h0)
    rw [(nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
    simp only [y, J2.apply_symm_apply, h0, f, a, zero_add]
  have hn := (hNative y h0).2.2.mp hyb
  obtain ⟨i, hi⟩ := hCover y h0 hp hn.le
  let x : E2 := (G (y, h0)).1
  have hx : ‖x‖ = 1 := (hLevel i (y, h0) hi).2.2.mpr hn
  have hxU (t : ℝ) (ht : t ∈ I) : (x, t) ∈ U :=
    hCylinder ⟨mem_closedBall_zero_iff.mpr hx.le, ht⟩
  let v : ℝ → E3 := fun t => !₂[r t * X x, eps i * Real.sqrt (energy (x, t)), w (x, t)]
  have hvnorm (t : ℝ) (ht : t ∈ I) : ‖v t‖ = 1 := by
    have hsq : ‖v t‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      change (r t * X x) ^ 2 + (eps i * Real.sqrt (energy (x, t))) ^ 2 + (w (x, t)) ^ 2 = 1
      rw [hepsSq, Real.sq_sqrt (hxU t ht).2.2.le]
      dsimp only [energy]; ring
    nlinarith only [hsq, norm_nonneg (v t)]
  have hvne (t : ℝ) (ht : t ∈ I) : v t ≠ 0 := by
    intro hv0; have h1 := hvnorm t ht; rw [hv0, norm_zero] at h1; norm_num at h1
  let gamma : ℝ → UnitTwoSphere := fun t => sphereDirection (v t)
  have hcoe (t : ℝ) (ht : t ∈ I) : (gamma t : E3) = v t := by
    exact (sphereDirection_coe (hvne t ht)).trans
      (NormedSpace.normalize_eq_self_of_norm_eq_one (hvnorm t ht))
  have hheight (t : ℝ) (ht : t ∈ I) : f (gamma t) = t := by
    have hxu := hxU t ht
    have hw := hinvL (r t * Y x) hxu.2.1
    change w (x, t) ∈ Ioo (-1 : ℝ) 0 ∧ L (w (x, t)) = r t * Y x at hw
    have hls := hLsq (w (x, t)) (hmemL _ hw.1)
    have hroot := Real.sq_sqrt hxu.2.2.le
    have hcoords : (X x) ^ 2 + (Y x) ^ 2 = 1 := by rw [hXY, hx]; norm_num
    have hscaled := congrArg (fun z : ℝ => (r t) ^ 2 * z) hcoords
    have harg : (r t * X x) ^ 2 + (eps i * Real.sqrt (energy (x, t))) ^ 2 =
        1 - (w (x, t)) ^ 2 := by
      rw [hepsSq, hroot]
      dsimp only [energy]; ring
    change 1 + (gamma t : E3) 2 - ((gamma t : E3) 1) ^ 2 +
      d (((gamma t : E3) 0) ^ 2 + ((gamma t : E3) 1) ^ 2) = t
    rw [hcoe t ht]
    change 1 + w (x, t) - (eps i * Real.sqrt (energy (x, t))) ^ 2 +
      d ((r t * X x) ^ 2 + (eps i * Real.sqrt (energy (x, t))) ^ 2) = t
    rw [harg, hepsSq, hroot]
    rw [hw.2] at hls
    dsimp only [energy]
    nlinarith only [hls, hscaled, (hr t ht).2.1]
  have hvsm : ContDiffOn ℝ ∞ v I := by
    have hmap : MapsTo (fun t : ℝ => (x, t)) I U0 := fun t ht => hUU0 (hxU t ht)
    have hw0 := hwsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn hmap
    have he0 := hesm.comp (contDiff_const.prodMk contDiff_id).contDiffOn hmap
    apply (contDiffOn_piLp 2).mpr
    intro j; fin_cases j
    · exact hrsm.mul contDiffOn_const
    · exact contDiffOn_const.mul (he0.sqrt (fun t ht => (hxU t ht).2.2.ne'))
    · exact hw0
  have hgammasm : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ gamma I :=
    sphereDirection_contMDiffOn.comp hvsm.contMDiffOn (fun t ht => hvne t ht)
  have hgammap : gamma h0 = p := by
    apply Subtype.ext
    apply (nonnestedReferenceDiffeomorph 0 d hd).injective
    change nonnestedReferenceDiffeomorph 0 d hd (gamma h0 : E3) =
      nonnestedReferenceDiffeomorph 0 d hd (p : E3)
    rw [(nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1 (gamma h0 : E3),
      (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1 (p : E3)]
    simp only [zero_add]
    apply Prod.ext
    · have hproj : (F i (x, h0)).1 = y := congrArg Prod.fst (hFG i (y, h0) hi)
      calc
        ((gamma h0 : E3) 0 / Real.sqrt 2, (gamma h0 : E3) 1 / Real.sqrt 2) =
            J2 (F i (x, h0)).1 := by rw [hcoe h0 hp]; simp only [F, J2.apply_symm_apply]; rfl
        _ = J2 y := congrArg J2 hproj
        _ = ((p : E3) 0 / Real.sqrt 2, (p : E3) 1 / Real.sqrt 2) := J2.apply_symm_apply _
    · change f (gamma h0) = f p
      exact hheight h0 hp
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun z : E3 => z j) := contDiff_piLp_apply 2
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    ((((contDiff_const.add (hc 2)).sub ((hc 1).pow 2)).add
      (hd.comp (((hc 0).pow 2).add ((hc 1).pow 2)))).contMDiff).comp contMDiff_coe_sphere
  have hident : f ∘ gamma =ᶠ[𝓝 h0] id := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with t ht
    exact hheight t ht
  have hchain : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ gamma) h0 : ℝ →L[ℝ] ℝ) =
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (gamma h0) : E2 →L[ℝ] ℝ).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) gamma h0 : ℝ →L[ℝ] E2) :=
    mfderiv_comp h0 (hf.mdifferentiable (by simp) (gamma h0))
      ((hgammasm.contMDiffAt (isOpen_Ioo.mem_nhds hp)).mdifferentiableAt (by simp))
  intro hzero
  have hfzero : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (gamma h0) = 0 := hgammap.symm ▸ hzero
  rw [hident.mfderiv_eq, mfderiv_id, hfzero, ContinuousLinearMap.zero_comp] at hchain
  have hbad := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1) hchain
  change (1 : ℝ) = 0 at hbad
  exact one_ne_zero hbad

end PoincareConjecture.M25.Topology3D
