import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCylinderArea
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPolarDescent












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ





def scalarStandardCylinderMap (p : Plane) : Plane :=
  scalarCoverMap (scalarCylinderCoordinate p + (1, 0))




theorem scalarStandardCylinderMap_smooth : ContDiff ℝ ∞ scalarStandardCylinderMap :=
  scalarCoverMap_smooth.comp (scalarCylinderCoordinate.contDiff.add contDiff_const)





theorem scalarStandardCylinderMap_mem {p : Plane} (hp : p 1 ∈ Ioo (0 : ℝ) 1) :
    scalarStandardCylinderMap p ∈ scalarAnnulus := by
  apply scalarCoverMap_mem
  change 1 < p 1 + 1 ∧ p 1 + 1 < 2
  constructor <;> linarith [hp.1, hp.2]





theorem scalarStandardCylinderMap_invertible {p : Plane} (hp : p 1 ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ scalarStandardCylinderMap p).IsInvertible := by
  have hz : (scalarCylinderCoordinate p + (1, 0)).1 ≠ 0 := by
    change p 1 + 1 ≠ 0
    linarith [hp.1]
  obtain ⟨A, hA⟩ := scalarCoverMap_fderiv_invertible hz
  have hsurj : Function.Surjective scalarCylinderCoordinate :=
    fun y => ⟨annulusPoint (curvePeriod * y.2) y.1, scalarCylinderCoordinate_right_inverse y⟩
  let B : Plane ≃L[ℝ] Cover :=
    (LinearEquiv.ofBijective scalarCylinderCoordinate.toLinearMap
      ⟨scalarCylinderCoordinate_injective, hsurj⟩).toContinuousLinearEquiv
  have hD := (scalarCoverMap_smooth.differentiable (by simp)
    (scalarCylinderCoordinate p + (1, 0))).hasFDerivAt.comp p
      (scalarCylinderCoordinate.hasFDerivAt.add_const (1, 0))
  refine ⟨B.trans A, ?_⟩
  change A.toContinuousLinearMap.comp B.toContinuousLinearMap = _
  rw [show fderiv ℝ scalarStandardCylinderMap p =
    (fderiv ℝ scalarCoverMap (scalarCylinderCoordinate p + (1, 0))).comp
      scalarCylinderCoordinate from hD.fderiv, ← hA]
  rfl





theorem scalarStandardCylinderMap_injOn :
    InjOn scalarStandardCylinderMap scalarCylinderFundamental := by
  intro p hp q hq hpq
  have hpcoord := scalarCylinderCoordinate_mem_fundamental hp
  have hqcoord := scalarCylinderCoordinate_mem_fundamental hq
  obtain ⟨k, hk⟩ := scalarCoverMap_fiber_of_pos
    (z := scalarCylinderCoordinate p + (1, 0)) (w := scalarCylinderCoordinate q + (1, 0))
    (by change 0 < p 1 + 1; linarith [hp.1.1])
    (by change 0 < q 1 + 1; linarith [hq.1.1]) hpq
  have hk2 : (scalarCylinderCoordinate p).2 = (scalarCylinderCoordinate q).2 + (k : ℝ) := by
    simpa only [Prod.snd_add, add_zero] using congrArg Prod.snd hk
  have hlo : (-1 : ℝ) < (k : ℝ) := by linarith [hpcoord.2.1, hqcoord.2.2]
  have hhi : (k : ℝ) < 1 := by linarith [hpcoord.2.2, hqcoord.2.1]
  have hlo' : (-1 : ℤ) < k := by exact_mod_cast hlo
  have hhi' : k < 1 := by exact_mod_cast hhi
  have hk0 : k = 0 := by omega
  have hcoord : scalarCylinderCoordinate p + (1, 0) =
      scalarCylinderCoordinate q + (1, 0) := by
    simpa only [hk0, Int.cast_zero, Prod.mk_zero_zero, add_zero] using hk
  exact scalarCylinderCoordinate_injective (add_right_cancel hcoord)





theorem scalarStandardCylinderMap_image :
    scalarStandardCylinderMap '' scalarCylinderFundamental = scalarAnnulus := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact scalarStandardCylinderMap_mem hq.1
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjOn hp
    let k : ℤ := ⌊z.2⌋
    let q : Plane := annulusPoint (curvePeriod * (z.2 - (k : ℝ))) (z.1 - 1)
    have hfrac : z.2 - (k : ℝ) ∈ Ico (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hq : q ∈ scalarCylinderFundamental := by
      change (0 < z.1 - 1 ∧ z.1 - 1 < 1) ∧
        0 ≤ curvePeriod * (z.2 - (k : ℝ)) ∧ curvePeriod * (z.2 - (k : ℝ)) < curvePeriod
      exact ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩,
        mul_nonneg hP.le hfrac.1, by nlinarith [hfrac.2]⟩
    refine ⟨q, hq, ?_⟩
    have hcoord : scalarCylinderCoordinate q + (1, 0) = (z.1, z.2 - (k : ℝ)) := by
      simp only [q, scalarCylinderCoordinate_apply, annulusPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one, Prod.mk_add_mk, sub_add_cancel, add_zero,
        ← mul_assoc, inv_mul_cancel₀ hP.ne', one_mul]
    have hperiod : Function.Periodic (fun t : ℝ => scalarCoverMap (z.1, t)) 1 := by
      intro t
      simpa only [Prod.mk_add_mk, add_zero] using scalarCoverMap_periodic (z.1, t)
    rw [scalarStandardCylinderMap, hcoord]
    simpa only [mul_one, Prod.eta] using hperiod.sub_int_mul_eq (x := z.2) k

end PoincareConjecture.M64Uniformization
