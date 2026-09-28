import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

noncomputable def nestedReferenceDiffeomorph (d : ℝ) :
    Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ := by
  let F : E3 → E3 := fun y =>
    !₂[y 0, y 1, y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d]
  let G : E3 → E3 := fun y =>
    !₂[y 0, y 1, y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d]
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun y : E3 => y i) :=
    contDiff_piLp_apply 2
  have hF : ContDiff ℝ ∞ F := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact hc 0
    · exact hc 1
    · exact ((((hc 2).add ((hc 0).pow 2)).add ((hc 1).pow 2)).add
        ((hc 0).div_const 32)).add contDiff_const
  have hG : ContDiff ℝ ∞ G := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact hc 0
    · exact hc 1
    · exact ((((hc 2).sub ((hc 0).pow 2)).sub ((hc 1).pow 2)).sub
        ((hc 0).div_const 32)).sub contDiff_const
  exact {
    toEquiv := {
      toFun := F
      invFun := G
      left_inv := by
        intro y
        ext i
        fin_cases i
        · rfl
        · rfl
        · change (y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d) -
            (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d = y 2
          ring
      right_inv := by
        intro y
        ext i
        fin_cases i
        · rfl
        · rfl
        · change (y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d) +
            (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d = y 2
          ring }
    contMDiff_toFun := hF.contMDiff
    contMDiff_invFun := hG.contMDiff }

theorem nestedReferenceDiffeomorph_apply_symm (d : ℝ) :
    (∀ y : E3, nestedReferenceDiffeomorph d y =
      !₂[y 0, y 1, y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d]) ∧
    (∀ y : E3, (nestedReferenceDiffeomorph d).symm y =
      !₂[y 0, y 1, y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d]) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

noncomputable def nestedReferenceBallChart (d : ℝ) :
    BallNeighborhoodChart E3 E3 where
  chart := (nestedReferenceDiffeomorph d).toHomeomorph.toOpenPartialHomeomorph
  closedBall_subset_source := subset_univ _
  smooth := (nestedReferenceDiffeomorph d).contDiff.contDiffOn
  smooth_symm := (nestedReferenceDiffeomorph d).symm.contDiff.contDiffOn

theorem nestedReferenceBallChart_regions (d : ℝ) :
    (nestedReferenceBallChart d).chart =
      (nestedReferenceDiffeomorph d).toHomeomorph.toOpenPartialHomeomorph ∧
    (nestedReferenceBallChart d).chart.source = Set.univ ∧
    (nestedReferenceBallChart d).chart.target = Set.univ ∧
    ∀ y : E3,
      (y ∈ (nestedReferenceBallChart d).inside ↔
        (y 0) ^ 2 + (y 1) ^ 2 +
          (y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d) ^ 2 < 1) ∧
      (y ∈ (nestedReferenceBallChart d).closedRegion ↔
        (y 0) ^ 2 + (y 1) ^ 2 +
          (y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d) ^ 2 ≤ 1) ∧
      (y ∈ (nestedReferenceBallChart d).boundary ↔
        (y 0) ^ 2 + (y 1) ^ 2 +
          (y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d) ^ 2 = 1) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro y
  let F := nestedReferenceDiffeomorph d
  have himage (T : Set E3) : y ∈ F '' T ↔ F.symm y ∈ T := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [F.symm_apply_apply] using hx
    · intro hy
      exact ⟨F.symm y, hy, F.apply_symm_apply y⟩
  have hnorm : ‖F.symm y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 +
      (y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d) ^ 2 := by
    rw [(nestedReferenceDiffeomorph_apply_symm d).2 y,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rfl
  change (y ∈ F '' ball 0 1 ↔ _) ∧ (y ∈ F '' closedBall 0 1 ↔ _) ∧
    (y ∈ F '' sphere 0 1 ↔ _)
  simp only [himage, mem_ball_zero_iff, mem_closedBall_zero_iff,
    mem_sphere_zero_iff_norm, ← hnorm]
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro hy <;>
    nlinarith only [norm_nonneg (F.symm y), hy]

theorem exists_unique_nestedReference_saddle_root :
    ∃! w : ℝ,
      1 / 2 < w ∧ w < 3 / 4 ∧
        (2 - 1 / w) * Real.sqrt (1 - w ^ 2) = 1 / 32 := by
  let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
  have hderivative (w : ℝ) (hw : w ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
      HasDerivAt g ((1 - 2 * w ^ 3) /
        (w ^ 2 * Real.sqrt (1 - w ^ 2))) w ∧
      0 < (1 - 2 * w ^ 3) / (w ^ 2 * Real.sqrt (1 - w ^ 2)) := by
    have hw0 : 0 < w :=
      lt_of_lt_of_le (show (0 : ℝ) < 1 / 2 by norm_num) hw.1
    have hsq := pow_le_pow_left₀ hw0.le hw.2 2
    have hcube := pow_le_pow_left₀ hw0.le hw.2 3
    norm_num at hsq hcube
    have hrad0 : 0 < 1 - w ^ 2 := by linarith only [hsq]
    have hnum0 : 0 < 1 - 2 * w ^ 3 := by linarith only [hcube]
    let s : ℝ := Real.sqrt (1 - w ^ 2)
    have hs0 : 0 < s := Real.sqrt_pos.mpr hrad0
    have hs2 : s ^ 2 = 1 - w ^ 2 := Real.sq_sqrt hrad0.le
    have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / w ^ 2) w :=
      (hasDerivAt_id w).inv hw0.ne'
    have ha : HasDerivAt (fun x : ℝ => 2 - 1 / x) (1 / w ^ 2) w := by
      simpa only [one_div, neg_div, neg_neg] using hinv.const_sub (2 : ℝ)
    have hrad : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * w) w := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one, neg_mul] using
        ((hasDerivAt_id w).pow 2).const_sub (1 : ℝ)
    have hraw : HasDerivAt g
        ((1 / w ^ 2) * s + (2 - 1 / w) * ((-2 * w) / (2 * s))) w :=
      ha.mul (hrad.sqrt hrad0.ne')
    have hcoefficient :
        (1 / w ^ 2) * s + (2 - 1 / w) * ((-2 * w) / (2 * s)) =
          (1 - 2 * w ^ 3) / (w ^ 2 * s) := by
      calc
        (1 / w ^ 2) * s + (2 - 1 / w) * ((-2 * w) / (2 * s)) =
            s ^ 2 / (w ^ 2 * s) +
              (w ^ 2 - 2 * w ^ 3) / (w ^ 2 * s) := by
          congr 1
          · field_simp [hw0.ne', hs0.ne']
          · field_simp [hw0.ne', hs0.ne']
            ring
        _ = (1 - 2 * w ^ 3) / (w ^ 2 * s) := by
          rw [← add_div]
          congr 1
          nlinarith only [hs2]
    rw [hcoefficient] at hraw
    exact ⟨hraw, div_pos hnum0 (mul_pos (pow_pos hw0 2) hs0)⟩
  have hcontinuous : ContinuousOn g (Icc (1 / 2 : ℝ) (3 / 4)) := by
    intro w hw
    exact (hderivative w hw).1.continuousAt.continuousWithinAt
  have hmono : StrictMonoOn g (Icc (1 / 2 : ℝ) (3 / 4)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcontinuous
    intro w hw
    obtain ⟨hd, hp⟩ := hderivative w (interior_subset hw)
    rw [hd.deriv]
    exact hp
  have hleft : g (1 / 2) < 1 / 32 := by
    norm_num [g]
  have hright : (1 / 32 : ℝ) < g (3 / 4) := by
    have hs0 := Real.sqrt_nonneg (1 - (3 / 4 : ℝ) ^ 2)
    have hs2 := Real.sq_sqrt
      (show (0 : ℝ) ≤ 1 - (3 / 4 : ℝ) ^ 2 by norm_num)
    have hs : (1 / 2 : ℝ) < Real.sqrt (1 - (3 / 4 : ℝ) ^ 2) := by
      nlinarith only [hs0, hs2]
    change (1 / 32 : ℝ) <
      (2 - 1 / (3 / 4 : ℝ)) * Real.sqrt (1 - (3 / 4 : ℝ) ^ 2)
    rw [show (2 - 1 / (3 / 4 : ℝ)) = 2 / 3 by norm_num]
    nlinarith only [hs]
  obtain ⟨w, hw, hroot⟩ := intermediate_value_Icc
    (show (1 / 2 : ℝ) ≤ 3 / 4 by norm_num) hcontinuous
    (show (1 / 32 : ℝ) ∈ Icc (g (1 / 2)) (g (3 / 4)) from
      ⟨hleft.le, hright.le⟩)
  have hwlower : (1 / 2 : ℝ) < w := by
    by_contra h
    have heq : w = 1 / 2 := le_antisymm (le_of_not_gt h) hw.1
    have hbad : g (1 / 2) = 1 / 32 := by simpa only [heq] using hroot
    exact (ne_of_lt hleft) hbad
  have hwupper : w < (3 / 4 : ℝ) := by
    by_contra h
    have heq : w = 3 / 4 := le_antisymm hw.2 (le_of_not_gt h)
    have hbad : g (3 / 4) = 1 / 32 := by simpa only [heq] using hroot
    exact (ne_of_gt hright) hbad
  refine ⟨w, ⟨hwlower, hwupper, hroot⟩, ?_⟩
  intro v hv
  have hvclosed : v ∈ Icc (1 / 2 : ℝ) (3 / 4) := ⟨hv.1.le, hv.2.1.le⟩
  have hvg : g v = 1 / 32 := hv.2.2
  rcases lt_trichotomy v w with hvw | heq | hwv
  · have hbad := hmono hvclosed hw hvw
    rw [hvg, hroot] at hbad
    exact False.elim ((lt_irrefl (1 / 32 : ℝ)) hbad)
  · exact heq
  · have hbad := hmono hw hvclosed hwv
    rw [hroot, hvg] at hbad
    exact False.elim ((lt_irrefl (1 / 32 : ℝ)) hbad)

end PoincareConjecture.M25.Topology3D
