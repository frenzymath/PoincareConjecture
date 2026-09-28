import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.AmbientMorseChart
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



noncomputable def nonnestedReferenceDiffeomorph
    (c : ℝ) (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d) :
    Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, (ℝ × ℝ) × ℝ)
      E3 ((ℝ × ℝ) × ℝ) ∞ := by
  let a : ℝ := Real.sqrt 2
  have ha : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : a ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let F (y : E3) : (ℝ × ℝ) × ℝ :=
    ((y 0 / a, y 1 / a), c + 1 + y 2 - (y 1) ^ 2 + d ((y 0) ^ 2 + (y 1) ^ 2))
  let G (p : (ℝ × ℝ) × ℝ) : E3 :=
    !₂[a * p.1.1, a * p.1.2,
      p.2 - c - 1 + 2 * p.1.2 ^ 2 - d (2 * (p.1.1 ^ 2 + p.1.2 ^ 2))]
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun y : E3 => y i) :=
    contDiff_piLp_apply 2
  have hF : ContDiff ℝ ∞ F := by
    exact ((hc 0).div_const a |>.prodMk ((hc 1).div_const a)).prodMk
      (((contDiff_const.add (hc 2)).sub ((hc 1).pow 2)).add
        (hd.comp (((hc 0).pow 2).add ((hc 1).pow 2))))
  have hG : ContDiff ℝ ∞ G := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const.mul contDiff_fst.fst
    · exact contDiff_const.mul contDiff_fst.snd
    · exact (((contDiff_snd.sub contDiff_const).sub contDiff_const).add
        (contDiff_const.mul (contDiff_fst.snd.pow 2))).sub
        (hd.comp (contDiff_const.mul
          ((contDiff_fst.fst.pow 2).add (contDiff_fst.snd.pow 2))))
  have hquot (x : ℝ) : 2 * (x / a) ^ 2 = x ^ 2 := by
    rw [div_pow, ha2]
    ring
  exact {
    toEquiv := {
      toFun := F
      invFun := G
      left_inv := by
        intro y
        ext i
        fin_cases i
        · change a * (y 0 / a) = y 0
          field_simp [ha.ne']
        · change a * (y 1 / a) = y 1
          field_simp [ha.ne']
        · change c + 1 + y 2 - (y 1) ^ 2 + d ((y 0) ^ 2 + (y 1) ^ 2) - c - 1 +
            2 * (y 1 / a) ^ 2 - d (2 * ((y 0 / a) ^ 2 + (y 1 / a) ^ 2)) = y 2
          rw [mul_add, hquot, hquot]
          ring
      right_inv := by
        rintro ⟨⟨s, t⟩, z⟩
        apply Prod.ext
        · apply Prod.ext
          · change a * s / a = s
            field_simp [ha.ne']
          · change a * t / a = t
            field_simp [ha.ne']
        · change c + 1 + (z - c - 1 + 2 * t ^ 2 - d (2 * (s ^ 2 + t ^ 2))) -
            (a * t) ^ 2 + d ((a * s) ^ 2 + (a * t) ^ 2) = z
          have hsum : (a * s) ^ 2 + (a * t) ^ 2 = 2 * (s ^ 2 + t ^ 2) := by
            rw [mul_pow, mul_pow, ha2]
            ring
          rw [hsum, mul_pow, ha2]
          ring }
    contMDiff_toFun := hF.contMDiff
    contMDiff_invFun := hG.contMDiff }



theorem nonnestedReferenceDiffeomorph_apply_symm
    (c : ℝ) (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d) :
    (∀ y : E3, nonnestedReferenceDiffeomorph c d hd y =
      ((y 0 / Real.sqrt 2, y 1 / Real.sqrt 2),
        c + 1 + y 2 - (y 1) ^ 2 + d ((y 0) ^ 2 + (y 1) ^ 2))) ∧
    (∀ p : (ℝ × ℝ) × ℝ,
      (nonnestedReferenceDiffeomorph c d hd).symm p =
        !₂[Real.sqrt 2 * p.1.1, Real.sqrt 2 * p.1.2,
          p.2 - c - 1 + 2 * p.1.2 ^ 2 -
            d (2 * (p.1.1 ^ 2 + p.1.2 ^ 2))]) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩



noncomputable def nonnestedReferenceBallChart
    (c : ℝ) (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d) :
    BallNeighborhoodChart E3 ((ℝ × ℝ) × ℝ) where
  chart := (nonnestedReferenceDiffeomorph c d hd).toHomeomorph.toOpenPartialHomeomorph
  closedBall_subset_source := subset_univ _
  smooth := (nonnestedReferenceDiffeomorph c d hd).contDiff.contDiffOn
  smooth_symm := (nonnestedReferenceDiffeomorph c d hd).symm.contDiff.contDiffOn



theorem nonnestedReferenceBallChart_regions
    (c : ℝ) (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d) :
    (nonnestedReferenceBallChart c d hd).chart.source = Set.univ ∧
    (nonnestedReferenceBallChart c d hd).chart.target = Set.univ ∧
    ∀ p : (ℝ × ℝ) × ℝ,
      (p ∈ (nonnestedReferenceBallChart c d hd).inside ↔
        2 * (p.1.1 ^ 2 + p.1.2 ^ 2) +
          (p.2 - c - 1 + 2 * p.1.2 ^ 2 -
            d (2 * (p.1.1 ^ 2 + p.1.2 ^ 2))) ^ 2 < 1) ∧
      (p ∈ (nonnestedReferenceBallChart c d hd).closedRegion ↔
        2 * (p.1.1 ^ 2 + p.1.2 ^ 2) +
          (p.2 - c - 1 + 2 * p.1.2 ^ 2 -
            d (2 * (p.1.1 ^ 2 + p.1.2 ^ 2))) ^ 2 ≤ 1) ∧
      (p ∈ (nonnestedReferenceBallChart c d hd).boundary ↔
        2 * (p.1.1 ^ 2 + p.1.2 ^ 2) +
          (p.2 - c - 1 + 2 * p.1.2 ^ 2 -
            d (2 * (p.1.1 ^ 2 + p.1.2 ^ 2))) ^ 2 = 1) := by
  refine ⟨rfl, rfl, ?_⟩
  intro p
  let F := nonnestedReferenceDiffeomorph c d hd
  have himage (T : Set E3) : p ∈ F '' T ↔ F.symm p ∈ T := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [F.symm_apply_apply] using hy
    · intro hp
      exact ⟨F.symm p, hp, F.apply_symm_apply p⟩
  have hnorm : ‖F.symm p‖ ^ 2 = 2 * (p.1.1 ^ 2 + p.1.2 ^ 2) +
      (p.2 - c - 1 + 2 * p.1.2 ^ 2 - d (2 * (p.1.1 ^ 2 + p.1.2 ^ 2))) ^ 2 := by
    rw [(nonnestedReferenceDiffeomorph_apply_symm c d hd).2 p,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    change (Real.sqrt 2 * p.1.1) ^ 2 + (Real.sqrt 2 * p.1.2) ^ 2 +
      (p.2 - c - 1 + 2 * p.1.2 ^ 2 - d (2 * (p.1.1 ^ 2 + p.1.2 ^ 2))) ^ 2 = _
    rw [mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  change (p ∈ F '' ball 0 1 ↔ _) ∧ (p ∈ F '' closedBall 0 1 ↔ _) ∧
    (p ∈ F '' sphere 0 1 ↔ _)
  rw [himage, himage, himage, mem_ball_zero_iff, mem_closedBall_zero_iff,
    mem_sphere_zero_iff_norm]
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro hp <;>
    nlinarith [norm_nonneg (F.symm p)]



theorem nonnestedReferenceBallChart_morse_box
    (c : ℝ) (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (rho : ℝ) (hrho : 0 < rho) (hrho_le : rho ≤ 1 / 16)
    (heq : ∀ q : ℝ, 0 ≤ q → q ≤ rho / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2) :
    ∀ p : (ℝ × ℝ) × ℝ,
      p.1.1 ^ 2 + p.1.2 ^ 2 < rho / 4 →
      |p.2 - c| < 1 / 8 →
      (p ∈ (nonnestedReferenceBallChart c d hd).inside ↔
        c + p.1.1 ^ 2 - p.1.2 ^ 2 < p.2) ∧
      (p ∈ (nonnestedReferenceBallChart c d hd).closedRegion ↔
        c + p.1.1 ^ 2 - p.1.2 ^ 2 ≤ p.2) ∧
      (p ∈ (nonnestedReferenceBallChart c d hd).boundary ↔
        p.2 = c + p.1.1 ^ 2 - p.1.2 ^ 2) := by
  intro p hp hz
  let r : ℝ := 2 * (p.1.1 ^ 2 + p.1.2 ^ 2)
  let v : ℝ := p.2 - c - p.1.1 ^ 2 + p.1.2 ^ 2
  let a : ℝ := Real.sqrt (1 - r)
  let N : ℝ := r + (p.2 - c - 1 + 2 * p.1.2 ^ 2 - d r) ^ 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrrho : r < rho / 2 := by dsimp [r]; linarith
  have hrsmall : r < 1 / 32 := lt_of_lt_of_le hrrho (by linarith)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
  have ha : 3 / 4 < a := by nlinarith
  have hvupper : v < 9 / 64 := by
    have hzp := (abs_lt.mp hz).2
    dsimp [v]
    nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
  have hnegative : v - 2 * a < 0 := by linarith
  have hdlocal : d r = a - 1 + r / 2 := heq r hr0 hrrho.le
  have hfactor : N - 1 = v * (v - 2 * a) := by
    dsimp only [N]
    rw [hdlocal]
    dsimp [v, r] at *
    nlinarith [ha2]
  obtain ⟨hi, hc, hb⟩ := (nonnestedReferenceBallChart_regions c d hd).2.2 p
  change (p ∈ (nonnestedReferenceBallChart c d hd).inside ↔ N < 1) at hi
  change (p ∈ (nonnestedReferenceBallChart c d hd).closedRegion ↔ N ≤ 1) at hc
  change (p ∈ (nonnestedReferenceBallChart c d hd).boundary ↔ N = 1) at hb
  rw [hi, hc, hb]
  have hgraph_lt : c + p.1.1 ^ 2 - p.1.2 ^ 2 < p.2 ↔ 0 < v := by
    dsimp [v]
    constructor <;> intro h <;> linarith
  have hgraph_le : c + p.1.1 ^ 2 - p.1.2 ^ 2 ≤ p.2 ↔ 0 ≤ v := by
    dsimp [v]
    constructor <;> intro h <;> linarith
  have hgraph_eq : p.2 = c + p.1.1 ^ 2 - p.1.2 ^ 2 ↔ v = 0 := by
    dsimp [v]
    constructor <;> intro h <;> linarith
  rw [hgraph_lt, hgraph_le, hgraph_eq]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      by_contra hv
      have hm := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hv) hnegative.le
      linarith
    · intro hv
      have hm := mul_neg_of_pos_of_neg hv hnegative
      linarith
  · constructor
    · intro h
      by_contra hv
      have hm := mul_pos_of_neg_of_neg (lt_of_not_ge hv) hnegative
      linarith
    · intro hv
      have hm := mul_nonpos_of_nonneg_of_nonpos hv hnegative.le
      linarith
  · constructor
    · intro h
      have hmul : v * (v - 2 * a) = 0 := by linarith
      exact (mul_eq_zero.mp hmul).resolve_right hnegative.ne
    · intro h
      rw [h, zero_mul] at hfactor
      linarith

end PoincareConjecture.M25.Topology3D
