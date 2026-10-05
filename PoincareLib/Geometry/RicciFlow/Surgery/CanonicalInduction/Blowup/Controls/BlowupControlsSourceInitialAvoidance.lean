import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceInitialInverse
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceInitialDistance

/-!
# Actual physical cap avoidance at the included birth

The tolerance is chosen from the fixed standard initial metric before
every physical flow. The original comparison chart remains distinct
from the event's cap chart.
Morgan--Tian Lemma 17.7, pp. 405-406;
blowup-source-initial-necks.md, I3C.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M47

/-- A tolerance fixed before the physical target excludes the actual
event cap from the comparison images of the quantitatively distant
initial points. Whole target-ball coverage is the original comparison
field, including at zero recent age. -/
theorem exists_source_initial_cap_avoidance_tolerance
    (g0 : StandardInitialMetric) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
      ∀ (i : Fin (F.event t hT).cap_count)
        (S : MaximalStandardCapFlow F.standard_initial) (A eta : ℝ) (J : Set ℝ)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
          ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
        (initial : SurgeryCapInitialComparison F t hT i A),
        SurgeryCapFamilyComparison F S A eta e initial.chart →
        ∀ hzero : (0 : ℝ) ∈ J,
          (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
            HEq (e.forward 0 hzero y) y) →
          0 < F.parameters.h t → 0 < eta → eta ≤ eta0 →
        ∀ x ∈ F.standard_initial.metric.ball 0 A,
          ENNReal.ofReal (F.standard_initial.cylindrical_end.radius + 104) ≤
            F.standard_initial.metric.edist 0 x →
          initial.chart x ∉ ((F.event t hT).caps i).carrier := by
  let Lambda := 1 + 1 / (g0.cylindrical_end.radius + 5)
  have hden : 0 < g0.cylindrical_end.radius + 5 := by
    linarith [g0.cylindrical_end.radius_pos]
  have hLambda : 1 < Lambda := by
    dsimp only [Lambda]
    linarith [one_div_pos.mpr hden]
  have hLambdaPos : 0 < Lambda := zero_lt_one.trans hLambda
  have hLambdaSq : 1 < Lambda ^ 2 := by nlinarith
  let eta0 := (Lambda ^ 2 - 1) / (2 * Lambda ^ 2)
  have heta0 : 0 < eta0 := div_pos (sub_pos.mpr hLambdaSq) (by positivity)
  refine ⟨eta0, heta0, ?_⟩
  intro F hinitial t hT hn i S A eta J e initial comparison hzero hbase hh heta hsmall x hx hfar
  have hbudget : 1 ≤ (1 - eta) * Lambda ^ 2 := by
    have heq : eta0 * (2 * Lambda ^ 2) = Lambda ^ 2 - 1 :=
      div_mul_cancel₀ _ (by positivity)
    have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg Lambda)
    nlinarith only [heq, hmul, hLambdaSq]
  have hd := source_initial_inverse_tip_distance initial.A_pos e initial comparison
    hzero hbase hh heta hLambdaPos hbudget hx
  intro hcap
  have houter := ((F.event t hT).caps i).outer_ball hcap
  have hrad : F.standard_initial.cylindrical_end.radius = g0.cylindrical_end.radius :=
    congrArg (fun g : StandardInitialMetric => g.cylindrical_end.radius) hinitial
  have houterReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top houter
  rw [ENNReal.toReal_ofReal (mul_nonneg hh.le
    (by linarith [F.standard_initial.cylindrical_end.radius_pos])), hrad] at houterReal
  have hfarReal := ENNReal.toReal_mono
    (F.standard_initial.metric.edist_ne_top 0 x) hfar
  rw [ENNReal.toReal_ofReal
    (by linarith [F.standard_initial.cylindrical_end.radius_pos]), hrad] at hfarReal
  have hupper : (F.standard_initial.metric.edist 0 x).toReal ≤
      g0.cylindrical_end.radius + 6 := by
    calc
      _ ≤ Lambda * (F.parameters.h t)⁻¹ *
          ((F.metric t).edist ((F.event t hT).caps i).tip (initial.chart x)).toReal := hd
      _ ≤ Lambda * (F.parameters.h t)⁻¹ *
          (F.parameters.h t * (g0.cylindrical_end.radius + 5)) :=
        mul_le_mul_of_nonneg_left houterReal (mul_nonneg hLambdaPos.le (inv_pos.mpr hh).le)
      _ = g0.cylindrical_end.radius + 6 := by
        dsimp only [Lambda]
        field_simp [hh.ne', hden.ne']
        ring
  linarith only [hfarReal, hupper]

end PoincareMT.M47
