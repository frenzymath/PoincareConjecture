import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "I2" => (modelWithCornersSelf Real E2)
local notation "CINF" => ((Top.top : ENat) : WithTop ENat)

noncomputable def southSpherePoint (x : E2) : UnitTwoSphere :=
  -northSpherePoint (-(HSMul.hSMul (Inv.inv (1 + Real.sqrt (1 - norm x ^ 2))) x))

theorem southSpherePoint_coordinates (x : E2) (hx : norm x < 1) :
    heightCoordinates (southSpherePoint x : E3) =
      (x, -Real.sqrt (1 - norm x ^ 2)) := by
  let s := Real.sqrt (1 - norm x ^ 2)
  let d := 1 + s
  let w := -(HSMul.hSMul (Inv.inv d) x)
  have hr : 0 < 1 - norm x ^ 2 := by nlinarith [norm_nonneg x]
  have hs : s ^ 2 = 1 - norm x ^ 2 := Real.sq_sqrt hr.le
  have hd : 0 < d := by dsimp [d, s]; positivity
  have hw : norm w ^ 2 = norm x ^ 2 / d ^ 2 := by
    dsimp only [w]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    ring
  have hD : 1 + norm w ^ 2 = 2 / d := by
    rw [hw]
    field_simp [hd.ne']
    dsimp only [d]
    nlinarith [hs]
  have hfactor : 2 / (1 + norm w ^ 2) * Inv.inv d = 1 := by
    rw [hD]
    field_simp [hd.ne']
  have hheight : (1 - norm w ^ 2) / (1 + norm w ^ 2) = s := by
    rw [hD, hw]
    field_simp [hd.ne']
    dsimp only [d]
    nlinarith [hs]
  change heightCoordinates ((-northSpherePoint w : UnitTwoSphere) : E3) = _
  rw [coe_neg_sphere, map_neg, northSpherePoint_coordinates]
  apply Prod.ext
  · change -(HSMul.hSMul (2 / (1 + norm w ^ 2))
      (-(HSMul.hSMul (Inv.inv d) x))) = x
    rw [smul_neg, smul_smul, hfactor, one_smul, neg_neg]
  · change -((1 - norm w ^ 2) / (1 + norm w ^ 2)) = -s
    rw [hheight]

theorem southSpherePoint_contMDiffOn :
    ContMDiffOn I2 I2 CINF southSpherePoint (Metric.ball (0 : E2) 1) := by
  let : Fact (Module.finrank Real E3 = 2 + 1) := Fact.mk (by simp [E3])
  have hr : ContDiff Real CINF (fun x : E2 => 1 - norm x ^ 2) :=
    contDiff_const.sub (contDiff_id.norm_sq Real)
  have hs : ContDiffOn Real CINF (fun x : E2 => Real.sqrt (1 - norm x ^ 2))
      (ball (0 : E2) 1) := hr.contDiffOn.sqrt (by
    intro x hx
    have hx1 := mem_ball_zero_iff.mp hx
    have hpos : 0 < 1 - norm x ^ 2 := by nlinarith [norm_nonneg x]
    exact hpos.ne')
  have hd : ContDiffOn Real CINF (fun x : E2 => 1 + Real.sqrt (1 - norm x ^ 2))
      (ball (0 : E2) 1) := contDiffOn_const.add hs
  have hw : ContDiffOn Real CINF
      (fun x : E2 => -(HSMul.hSMul (Inv.inv (1 + Real.sqrt (1 - norm x ^ 2))) x))
      (ball (0 : E2) 1) :=
    ((hd.inv (fun x _ => ne_of_gt (by positivity))).smul contDiffOn_id).neg
  exact contMDiff_neg_sphere.comp_contMDiffOn
    (northSpherePoint_contMDiff.comp_contMDiffOn hw.contMDiffOn)

theorem southSpherePoint_coordinate (q : UnitTwoSphere)
    (hq : (heightCoordinates (q : E3)).2 < 0) :
    And (norm (heightCoordinates (q : E3)).1 < 1)
      (southSpherePoint (heightCoordinates (q : E3)).1 = q) := by
  have hs := sphere_height_coordinates_sq q
  have hz : 0 < (heightCoordinates (q : E3)).2 ^ 2 := sq_pos_of_neg hq
  have hx : norm (heightCoordinates (q : E3)).1 < 1 := by
    nlinarith [norm_nonneg (heightCoordinates (q : E3)).1]
  refine And.intro hx ?_
  apply Subtype.ext
  apply heightCoordinates.injective
  rw [southSpherePoint_coordinates _ hx]
  have hr : 1 - norm (heightCoordinates (q : E3)).1 ^ 2 =
      (heightCoordinates (q : E3)).2 ^ 2 := by linarith
  rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hq, neg_neg]

noncomputable def southSphereChart : OpenPartialHomeomorph E2 UnitTwoSphere where
  toFun := southSpherePoint
  invFun := fun q => (heightCoordinates (q : E3)).1
  source := ball 0 1
  target := {q | (heightCoordinates (q : E3)).2 < 0}
  map_source' x hx := by
    change (heightCoordinates (southSpherePoint x : E3)).2 < 0
    rw [southSpherePoint_coordinates x (mem_ball_zero_iff.mp hx)]
    have hn := mem_ball_zero_iff.mp hx
    exact neg_neg_of_pos (Real.sqrt_pos.mpr (by nlinarith [norm_nonneg x]))
  map_target' q hq := mem_ball_zero_iff.mpr (southSpherePoint_coordinate q hq).1
  left_inv' x hx := by
    change (heightCoordinates (southSpherePoint x : E3)).1 = x
    rw [southSpherePoint_coordinates x (mem_ball_zero_iff.mp hx)]
  right_inv' q hq := (southSpherePoint_coordinate q hq).2
  open_source := isOpen_ball
  open_target := isOpen_lt
    (heightCoordinates.continuous.comp continuous_subtype_val).snd continuous_const
  continuousOn_toFun := southSpherePoint_contMDiffOn.continuousOn
  continuousOn_invFun :=
    (heightCoordinates.continuous.comp continuous_subtype_val).fst.continuousOn

theorem southSphereChart_contMDiff :
    And (ContMDiffOn I2 I2 CINF southSphereChart southSphereChart.source)
      (ContMDiffOn I2 I2 CINF southSphereChart.symm southSphereChart.target) := by
  let : Fact (Module.finrank Real E3 = 2 + 1) := Fact.mk (by simp [E3])
  refine And.intro southSpherePoint_contMDiffOn ?_
  have hc : ContMDiff I2 (modelWithCornersSelf Real (Prod E2 Real)) CINF
      (fun q : UnitTwoSphere => heightCoordinates (q : E3)) :=
    heightCoordinates.contDiff.contMDiff.comp contMDiff_coe_sphere
  exact (contDiff_fst.contMDiff.comp hc).contMDiffOn

end PoincareConjecture.M25.Topology3D
