import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.ShearSlices
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift.Reflection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

def tangentWallReflection : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  heightReflection (v := EuclideanSpace.single 0 1) (by simp)

theorem tangentWallReflection_apply (p : E3) :
    tangentWallReflection p = vector (-p 0) (p 1) (p 2) := by
  unfold tangentWallReflection heightReflection
  rw [liftPlaneDiffeomorph_apply]
  simp only [Diffeomorph.coe_refl, id_eq, zero_add, neg_one_mul]
  rw [Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton Real (by simp : ‖(EuclideanSpace.single 0 1 : E3)‖ = 1)]
  ext i
  fin_cases i <;> simp [vector, EuclideanSpace.inner_single_left]

@[simp] theorem tangentWallReflection_zero (p : E3) : tangentWallReflection p 0 = -p 0 := by
  rw [tangentWallReflection_apply]
  rfl

@[simp] theorem tangentWallReflection_one (p : E3) : tangentWallReflection p 1 = p 1 := by
  rw [tangentWallReflection_apply]
  rfl

@[simp] theorem tangentWallReflection_two (p : E3) : tangentWallReflection p 2 = p 2 := by
  rw [tangentWallReflection_apply]
  rfl

theorem tangentWallReflection_fixed {p : E3} (hp : p 0 = 0) : tangentWallReflection p = p := by
  ext i
  fin_cases i <;> simp [hp]

def tangentFlatRightBall : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  tangentFlatShear.trans tangentWallReflection

@[simp] theorem tangentFlatRightBall_zero (p : E3) :
    tangentFlatRightBall p 0 = -tangentFlatShear p 0 := tangentWallReflection_zero _

@[simp] theorem tangentFlatRightBall_one (p : E3) : tangentFlatRightBall p 1 = p 1 := by
  change tangentWallReflection (tangentFlatShear p) 1 = _
  simp

@[simp] theorem tangentFlatRightBall_two (p : E3) : tangentFlatRightBall p 2 = p 2 := by
  change tangentWallReflection (tangentFlatShear p) 2 = _
  simp

theorem tangentFlatRightBall_body_nonneg {y : E3}
    (hy : y ∈ tangentFlatRightBall '' closedBall (0 : E3) 1) : 0 ≤ y 0 := by
  obtain ⟨p, hp, rfl⟩ := hy
  rw [tangentFlatRightBall_zero]
  exact neg_nonneg.mpr (tangentFlatShear_body_nonpos (mem_image_of_mem _ hp))

theorem tangentFlatRightBall_sphere_nonneg {y : E3}
    (hy : y ∈ tangentFlatRightBall '' sphere (0 : E3) 1) : 0 ≤ y 0 :=
  tangentFlatRightBall_body_nonneg (image_mono sphere_subset_closedBall hy)

theorem tangentFlatPair_body_inter :
    (tangentFlatShear '' closedBall (0 : E3) 1) ∩
        (tangentFlatRightBall '' closedBall (0 : E3) 1) =
      {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1 / 4} := by
  ext y
  constructor
  · rintro ⟨hyl, hyr⟩
    have hzero : y 0 = 0 := le_antisymm (tangentFlatShear_body_nonpos hyl)
      (tangentFlatRightBall_body_nonneg hyr)
    exact tangentFlatShear_body_inter_wall ▸ ⟨hyl, hzero⟩
  · intro hy
    obtain ⟨hyl, hzero⟩ := tangentFlatShear_body_inter_wall.symm ▸ hy
    refine ⟨hyl, ?_⟩
    obtain ⟨p, hp, hpy⟩ := hyl
    exact ⟨p, hp, (congrArg tangentWallReflection hpy).trans (tangentWallReflection_fixed hzero)⟩

theorem tangentFlatPair_sphere_inter :
    (tangentFlatShear '' sphere (0 : E3) 1) ∩
        (tangentFlatRightBall '' sphere (0 : E3) 1) =
      {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1 / 4} := by
  ext y
  constructor
  · rintro ⟨hyl, hyr⟩
    have hzero : y 0 = 0 := le_antisymm
      (tangentFlatShear_body_nonpos (image_mono sphere_subset_closedBall hyl))
      (tangentFlatRightBall_sphere_nonneg hyr)
    exact tangentFlatShear_sphere_inter_wall ▸ ⟨hyl, hzero⟩
  · intro hy
    obtain ⟨hyl, hzero⟩ := tangentFlatShear_sphere_inter_wall.symm ▸ hy
    refine ⟨hyl, ?_⟩
    obtain ⟨p, hp, hpy⟩ := hyl
    exact ⟨p, hp, (congrArg tangentWallReflection hpy).trans (tangentWallReflection_fixed hzero)⟩

def tangentWallDisk (x : E2) : E3 := vector 0 (x 0 / 2) (x 1 / 2)

theorem contDiff_tangentWallDisk : ContDiff Real ∞ tangentWallDisk := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.div_const 2
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.div_const 2

theorem tangentWallDisk_injective : Injective tangentWallDisk := by
  intro x y he
  have h0 := congrArg (fun p : E3 => p 1) he
  have h1 := congrArg (fun p : E3 => p 2) he
  ext i
  fin_cases i
  · change x 0 = y 0
    change x 0 / 2 = y 0 / 2 at h0
    linarith
  · change x 1 = y 1
    change x 1 / 2 = y 1 / 2 at h1
    linarith

theorem tangentWallDisk_injective_fderiv (x : E2) : Injective (fderiv Real tangentWallDisk x) := by
  let L : E3 → E2 := fun p => WithLp.toLp 2 ![2 * p 1, 2 * p 2]
  have hL : ContDiff Real ∞ L := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
    · exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff
  have hleft : L ∘ tangentWallDisk = id := by
    funext q
    ext i
    fin_cases i <;> simp [L, tangentWallDisk, vector] <;> ring
  have hchain := fderiv_comp x (hL.differentiable (by simp) _)
    (contDiff_tangentWallDisk.differentiable (by simp) x)
  rw [hleft, fderiv_id] at hchain
  intro u v huv
  have he := congrArg (fderiv Real L (tangentWallDisk x)) huv
  change ((fderiv Real L (tangentWallDisk x)).comp (fderiv Real tangentWallDisk x)) u =
    ((fderiv Real L (tangentWallDisk x)).comp (fderiv Real tangentWallDisk x)) v at he
  rwa [← hchain] at he

theorem tangentWallDisk_image_closedBall :
    tangentWallDisk '' closedBall (0 : E2) 1 =
      {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1 / 4} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨rfl, ?_⟩
    have hn := mem_closedBall_zero_iff.mp hx
    have he := norm_sq_two x
    change (x 0 / 2) ^ 2 + (x 1 / 2) ^ 2 ≤ 1 / 4
    nlinarith [norm_nonneg x]
  · rintro ⟨hy0, hys⟩
    let x : E2 := WithLp.toLp 2 ![2 * y 1, 2 * y 2]
    have hx : x ∈ closedBall (0 : E2) 1 := by
      have hn : ‖x‖ ^ 2 = 4 * tangentRadiusSq y := by
        rw [norm_sq_two]
        change (2 * y 1) ^ 2 + (2 * y 2) ^ 2 = 4 * (y 1 ^ 2 + y 2 ^ 2)
        ring
      rw [mem_closedBall_zero_iff]
      nlinarith [norm_nonneg x]
    refine ⟨x, hx, ?_⟩
    ext i
    fin_cases i
    · exact hy0.symm
    · change 2 * y 1 / 2 = y 1
      ring
    · change 2 * y 2 / 2 = y 2
      ring

theorem tangentFlatPair_sphere_inter_eq_disk :
    (tangentFlatShear '' sphere (0 : E3) 1) ∩
        (tangentFlatRightBall '' sphere (0 : E3) 1) =
      tangentWallDisk '' closedBall (0 : E2) 1 :=
  tangentFlatPair_sphere_inter.trans tangentWallDisk_image_closedBall.symm

theorem tangentFlatPair_body_inter_eq_disk :
    (tangentFlatShear '' closedBall (0 : E3) 1) ∩
        (tangentFlatRightBall '' closedBall (0 : E3) 1) =
      tangentWallDisk '' closedBall (0 : E2) 1 :=
  tangentFlatPair_body_inter.trans tangentWallDisk_image_closedBall.symm

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
