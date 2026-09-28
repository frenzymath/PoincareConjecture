import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

private abbrev E3 := EuclideanSpace Real (Fin 3)

def tangentRadiusSq (p : E3) : Real := (p 1)^2 + (p 2)^2

def tangentFlattenCutoff (s : Real) : Real := 1 - Real.smoothTransition (4*s-1)

def tangentFlattenDepth (p : E3) : Real :=
  Real.sqrt (1 - tangentRadiusSq p * tangentFlattenCutoff (tangentRadiusSq p))

theorem tangentRadiusSq_nonneg (p : E3) : 0 ≤ tangentRadiusSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem tangentFlattenCutoff_bounds (s : Real) :
    0 ≤ tangentFlattenCutoff s ∧ tangentFlattenCutoff s ≤ 1 := by
  have h := Real.smoothTransition.nonneg (4*s-1)
  have h' := Real.smoothTransition.le_one (4*s-1)
  dsimp [tangentFlattenCutoff]
  constructor <;> linarith

theorem tangentFlattenDepth_radicand_pos (p : E3) :
    0 < 1 - tangentRadiusSq p * tangentFlattenCutoff (tangentRadiusSq p) := by
  by_cases hs : tangentRadiusSq p < 1/2
  · have hm := mul_le_mul_of_nonneg_left
      (tangentFlattenCutoff_bounds (tangentRadiusSq p)).2 (tangentRadiusSq_nonneg p)
    nlinarith
  · have he : tangentFlattenCutoff (tangentRadiusSq p) = 0 := by
      simp only [tangentFlattenCutoff,
        Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4*tangentRadiusSq p-1),
        sub_self]
    rw [he, mul_zero, sub_zero]
    norm_num

theorem contDiff_tangentFlattenDepth : ContDiff Real ∞ tangentFlattenDepth := by
  have hs : ContDiff Real ∞ tangentRadiusSq :=
    ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff.pow 2).add
      ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff.pow 2)
  have hχ : ContDiff Real ∞ tangentFlattenCutoff := contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  exact (contDiff_const.sub (hs.mul (hχ.comp hs))).sqrt
    (fun p => (tangentFlattenDepth_radicand_pos p).ne')

theorem tangentFlattenDepth_sq (p : E3) :
    tangentFlattenDepth p ^ 2 =
      1 - tangentRadiusSq p * tangentFlattenCutoff (tangentRadiusSq p) :=
  Real.sq_sqrt (tangentFlattenDepth_radicand_pos p).le

theorem tangentFlattenDepth_nonneg (p : E3) : 0 ≤ tangentFlattenDepth p :=
  Real.sqrt_nonneg _

def tangentFlatShear : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun p := p - tangentFlattenDepth p • EuclideanSpace.single 0 1
  invFun p := p + tangentFlattenDepth p • EuclideanSpace.single 0 1
  left_inv p := by ext i; simp [tangentFlattenDepth, tangentRadiusSq]
  right_inv p := by ext i; simp [tangentFlattenDepth, tangentRadiusSq]
  contMDiff_toFun :=
    (contDiff_id.sub (contDiff_tangentFlattenDepth.smul contDiff_const)).contMDiff
  contMDiff_invFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p : E3 =>
      p + tangentFlattenDepth p • EuclideanSpace.single 0 1)
    exact (contDiff_id.add (contDiff_tangentFlattenDepth.smul contDiff_const)).contMDiff

@[simp] theorem tangentFlatShear_zero (p : E3) :
    tangentFlatShear p 0 = p 0 - tangentFlattenDepth p := by
  change (p - tangentFlattenDepth p • (EuclideanSpace.single 0 1 : E3)) 0 = _
  simp

@[simp] theorem tangentFlatShear_one (p : E3) : tangentFlatShear p 1 = p 1 := by
  change (p - tangentFlattenDepth p • (EuclideanSpace.single 0 1 : E3)) 1 = _
  simp

@[simp] theorem tangentFlatShear_two (p : E3) : tangentFlatShear p 2 = p 2 := by
  change (p - tangentFlattenDepth p • (EuclideanSpace.single 0 1 : E3)) 2 = _
  simp

private theorem norm_sq_three (p : E3) : ‖p‖^2 = (p 0)^2 + tangentRadiusSq p := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, tangentRadiusSq, add_assoc]

theorem tangentFlatShear_body_nonpos {y : E3}
    (hy : y ∈ tangentFlatShear '' closedBall (0 : E3) 1) : y 0 ≤ 0 := by
  obtain ⟨p, hp, rfl⟩ := hy
  have hp' := mem_closedBall_zero_iff.mp hp
  have hn := norm_sq_three p
  have hd := tangentFlattenDepth_sq p
  have hnon := tangentFlattenDepth_nonneg p
  have hm := mul_le_mul_of_nonneg_left
    (tangentFlattenCutoff_bounds (tangentRadiusSq p)).2 (tangentRadiusSq_nonneg p)
  rw [tangentFlatShear_zero]
  nlinarith [norm_nonneg p]

theorem tangentFlatShear_body_inter_wall :
    (tangentFlatShear '' closedBall (0 : E3) 1) ∩ {p : E3 | p 0 = 0} =
      {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1/4} := by
  ext y
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hh⟩
    refine ⟨hh, ?_⟩
    have he : p 0 = tangentFlattenDepth p := by
      change tangentFlatShear p 0 = 0 at hh
      rw [tangentFlatShear_zero] at hh
      exact sub_eq_zero.mp hh
    have hp' := mem_closedBall_zero_iff.mp hp
    have hn := norm_sq_three p
    have hd := tangentFlattenDepth_sq p
    have hs : tangentRadiusSq p ≤ 1/4 := by
      by_contra hs
      have hpos := Real.smoothTransition.pos_of_pos
        (by linarith : 0 < 4*tangentRadiusSq p-1)
      have hχ : tangentFlattenCutoff (tangentRadiusSq p) < 1 := by
        dsimp [tangentFlattenCutoff]
        linarith
      have hm := mul_lt_mul_of_pos_left hχ
        (show 0 < tangentRadiusSq p by linarith)
      rw [he] at hn
      nlinarith [norm_nonneg p]
    simpa only [tangentRadiusSq, tangentFlatShear_one, tangentFlatShear_two] using hs
  · rintro ⟨hy0, hys⟩
    let p : E3 := y + tangentFlattenDepth y • EuclideanSpace.single 0 1
    have hp1 : p 1 = y 1 := by simp [p]
    have hp2 : p 2 = y 2 := by simp [p]
    have hps : tangentRadiusSq p = tangentRadiusSq y := by
      simp only [tangentRadiusSq, hp1, hp2]
    have hpd : tangentFlattenDepth p = tangentFlattenDepth y := by
      simp only [tangentFlattenDepth, hps]
    have hχ : tangentFlattenCutoff (tangentRadiusSq y) = 1 := by
      simp only [tangentFlattenCutoff,
        Real.smoothTransition.zero_of_nonpos (by linarith : 4*tangentRadiusSq y-1 ≤ 0),
        sub_zero]
    have hnorm : ‖p‖^2 = 1 := by
      rw [norm_sq_three, hps]
      have hp0 : p 0 = tangentFlattenDepth y := by simp [p, hy0]
      rw [hp0, tangentFlattenDepth_sq, hχ]
      ring
    refine ⟨⟨p, mem_closedBall_zero_iff.mpr (by nlinarith [norm_nonneg p]), ?_⟩, hy0⟩
    change p - tangentFlattenDepth p • EuclideanSpace.single 0 1 = y
    rw [hpd]
    exact add_sub_cancel_right _ _

theorem tangentFlatShear_sphere_inter_wall :
    (tangentFlatShear '' sphere (0 : E3) 1) ∩ {p : E3 | p 0 = 0} =
      {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1/4} := by
  ext y
  constructor
  · rintro ⟨hy, hh⟩
    exact tangentFlatShear_body_inter_wall ▸
      ⟨image_mono sphere_subset_closedBall hy, hh⟩
  · intro hy
    obtain ⟨⟨p, hp, rfl⟩, hh⟩ := tangentFlatShear_body_inter_wall.symm ▸ hy
    have he : p 0 = tangentFlattenDepth p := by
      change tangentFlatShear p 0 = 0 at hh
      rw [tangentFlatShear_zero] at hh
      exact sub_eq_zero.mp hh
    have hs : tangentRadiusSq p ≤ 1/4 := by
      simpa only [tangentRadiusSq, tangentFlatShear_one, tangentFlatShear_two] using hy.2
    have hχ : tangentFlattenCutoff (tangentRadiusSq p) = 1 := by
      simp only [tangentFlattenCutoff,
        Real.smoothTransition.zero_of_nonpos (by linarith : 4*tangentRadiusSq p-1 ≤ 0),
        sub_zero]
    have hnorm : ‖p‖^2 = 1 := by
      rw [norm_sq_three, he, tangentFlattenDepth_sq, hχ]
      ring
    refine ⟨⟨p, ?_, rfl⟩, hh⟩
    rw [mem_sphere, dist_zero_right]
    nlinarith [norm_nonneg p]

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
