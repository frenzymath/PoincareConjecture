import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialJoiningHeightPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem source_initial_recent_patch_height_margin
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {A eta Lambda L : ℝ}
    {J : Set ℝ} {V : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J V)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J) (hbase : ∀ y ∈ V, HEq (e.forward 0 hzero y) y)
    (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000) (hLambda : 0 < Lambda)
    (hLambdaSmall : Lambda ≤ 1001 / 1000)
    (hbudget : 1 ≤ (1 - ((F.event t hT).necks i).neck.epsilon) * Lambda ^ 2)
    (hL : 1200 ≤ L) {U : Set StandardCapSpace} (hU : IsOpen U)
    (hsource : U ⊆ F.standard_initial.metric.ball 0 A)
    (havoid : ∀ x ∈ U, initial.chart x ∉ ((F.event t hT).caps i).carrier)
    {p : ℝ → StandardCapSpace}
    (hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p (Icc 0 1))
    (himage : MapsTo p (Icc (0 : ℝ) 1) U)
    (hlen : F.standard_initial.metric.pathELength p 0 1 <
      ENNReal.ofReal (6 + L / 3)) :
    |(((F.event t hT).necks i).neck.coordinate_inverse
        (sourceInitialOldMap initial (p 1))).2 -
      (((F.event t hT).necks i).neck.coordinate_inverse
        (sourceInitialOldMap initial (p 0))).2| < 2 * L / 3 := by
  have hdist := source_initial_joining_height_path_length e initial comparison hzero hbase
    heta hetaSmall hLambda hbudget hU hsource havoid hp himage
  have hcoef : 0 ≤ (101 / 100 : ℝ) * Lambda := by positivity
  have hright : ENNReal.ofReal ((101 / 100 : ℝ) * Lambda) *
      F.standard_initial.metric.pathELength p 0 1 <
      ENNReal.ofReal ((101 / 100 : ℝ) * Lambda) * ENNReal.ofReal (6 + L / 3) := by
    exact ENNReal.mul_lt_mul_right
      (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hLambda)))
      ENNReal.ofReal_ne_top hlen
  have hlt := hdist.trans_lt hright
  have htop : ENNReal.ofReal ((101 / 100 : ℝ) * Lambda) * ENNReal.ofReal (6 + L / 3) <
      ENNReal.ofReal (2 * L / 3) := by
    rw [← ENNReal.ofReal_mul hcoef]
    apply (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hL])).mpr
    nlinarith only [hLambdaSmall, hL]
  have hlt' := hlt.trans htop
  have hreal := (ENNReal.toReal_lt_toReal (edist_ne_top _ _)
    ENNReal.ofReal_ne_top).mpr hlt'
  rw [ENNReal.toReal_ofReal (by linarith only [hL])] at hreal
  have hdistReal :
      |(((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial (p 1))).2 -
        (((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial (p 0))).2| =
      (edist
        (((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial (p 0))).2
        (((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial (p 1))).2).toReal := by
    rw [edist_dist, Real.dist_eq]
    simp only [ENNReal.toReal_ofReal (abs_nonneg _)]
    exact abs_sub_comm _ _
  calc
    _ = (edist
        (((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial (p 0))).2
        (((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial (p 1))).2).toReal := hdistReal
    _ < 2 * L / 3 := hreal

end PoincareConjecture.M47
