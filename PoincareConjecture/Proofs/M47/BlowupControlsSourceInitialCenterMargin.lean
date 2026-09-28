import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCarrierArithmetic
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialPhysicalTip
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthBall
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialAvoidance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

theorem exists_source_initial_older_center_margin
    (g0 : StandardInitialMetric) (gamma : ℝ)
    (hgamma : 0 < gamma) (hsmall : gamma ≤ 1 / 1200) :
    ∃ Lambda eta0 delta0 : ℝ,
      1 < Lambda ∧ Lambda < 1001 / 1000 ∧ 0 < eta0 ∧ 0 < delta0 ∧
      (∀ delta : ℝ, 0 ≤ delta → delta ≤ delta0 →
        Real.sqrt (1 + delta) ≤ Lambda ∧ 1 ≤ (1 - delta) * Lambda ^ 2) ∧
      (∀ eta : ℝ, eta ≤ eta0 → 1 ≤ (1 - eta) * Lambda ^ 2) ∧
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
          0 < eta → eta ≤ eta0 → ((F.event t hT).necks i).neck.epsilon ≤ delta0 →
        ∀ (atlas : StandardCylinderAtlas) (v : ℝ) (z : StandardCapSpace)
          (N : StandardEvolvingNeck atlas S v gamma z
            (Icc (-v * (S.connection v).scalarCurvature z) 0)),
          Disjoint N.patch.carrier
            {y | F.standard_initial.metric.edist 0 y ≤
              ENNReal.ofReal (F.standard_initial.cylindrical_end.radius + 4)} →
          v * (S.connection v).scalarCurvature z < 1 + gamma →
        ∀ x ∈ F.standard_initial.metric.ball 0 A, x ∈ N.patch.carrier →
          |(N.patch.inverse x).2| ≤ 1 →
          initial.chart x ∉ ((F.event t hT).caps i).carrier ∧
          (((F.event t hT).necks i).neck.coordinate_inverse
            (sourceInitialOldMap initial x)).2 + 2 * gamma⁻¹ / 3 < 0 := by
  have hL : (1200 : ℝ) ≤ gamma⁻¹ := by
    have h := inv_anti₀ hgamma hsmall
    norm_num at h
    exact h
  obtain ⟨Lambda, etaFactor, delta0, hLambda, hLambdaSmall, hetaFactor, hdelta0,
    hdelta, heta, hgap⟩ := exists_source_initial_carrier_factors
      g0.cylindrical_end.radius gamma⁻¹ g0.cylindrical_end.radius_pos hL
  obtain ⟨etaAvoid, hetaAvoid, havoidFactory⟩ :=
    exists_source_initial_cap_avoidance_tolerance g0
  let eta0 := min etaFactor etaAvoid
  have heta0 : 0 < eta0 := lt_min hetaFactor hetaAvoid
  refine ⟨Lambda, eta0, delta0, hLambda, hLambdaSmall, heta0, hdelta0, hdelta,
    (fun eta he => heta eta (he.trans (min_le_left _ _))), ?_⟩
  intro F hinitial t hT hn i S A eta J e initial comparison hzero hbase
    hetaPos hetaSmall hdeltaSmall atlas v z N hdisjoint hshort x hx hxN hheight
  let old := ((F.event t hT).necks i).neck
  let c := (old.coordinate_inverse (sourceInitialOldMap initial x)).2
  have hh : 0 < F.parameters.h t := (F.event t hT).neck_scale i ▸ old.scale_pos
  have hLambdaPos : 0 < Lambda := zero_lt_one.trans hLambda
  have hbudget := heta eta (hetaSmall.trans (min_le_left _ _))
  have hsqrt := (hdelta old.epsilon old.epsilon_pos.le hdeltaSmall).1
  have hrad : F.standard_initial.cylindrical_end.radius = g0.cylindrical_end.radius :=
    congrArg (fun g : StandardInitialMetric => g.cylindrical_end.radius) hinitial
  have hfar := standard_initial_neck_tip_distance_sharp N hsmall hdisjoint hshort hxN hheight
  have hfar104 : ENNReal.ofReal (F.standard_initial.cylindrical_end.radius + 104) ≤
      F.standard_initial.metric.edist 0 x :=
    (ENNReal.ofReal_le_ofReal (by linarith only [hL])).trans hfar
  have havoid := havoidFactory F hinitial t hT i S A eta J e initial comparison
    hzero hbase hh hetaPos (hetaSmall.trans (min_le_right _ _)) x hx hfar104
  have hret := source_initial_chart_retention hT i initial hx havoid
  have hc : c < 0 := hret.2.2.2.2
  have hphysical := source_initial_physical_tip_distance_upper hT i initial hx havoid
  have hinverse := source_initial_inverse_tip_distance initial.A_pos e initial comparison
    hzero hbase hh hetaPos hLambdaPos hbudget hx
  have hphysicalReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hphysical
  rw [ENNReal.toReal_ofReal (mul_nonneg hh.le
    (show 0 ≤ F.standard_initial.cylindrical_end.radius + 5 +
        Real.sqrt (1 + old.epsilon) * |c| by
      have h := mul_nonneg (Real.sqrt_nonneg (1 + old.epsilon)) (abs_nonneg c)
      linarith only [h, F.standard_initial.cylindrical_end.radius_pos]))] at hphysicalReal
  have hfarReal := ENNReal.toReal_mono (F.standard_initial.metric.edist_ne_top 0 x) hfar
  rw [ENNReal.toReal_ofReal (by linarith only
    [hL, F.standard_initial.cylindrical_end.radius_pos]), hrad] at hfarReal
  refine ⟨havoid, ?_⟩
  change c + 2 * gamma⁻¹ / 3 < 0
  by_contra hnot
  have habs : |c| ≤ 2 * gamma⁻¹ / 3 := by
    rw [abs_of_neg hc]
    linarith only [le_of_not_gt hnot]
  have hupper : (F.standard_initial.metric.edist 0 x).toReal ≤
      Lambda * (g0.cylindrical_end.radius + 5 + Lambda * (2 * gamma⁻¹ / 3)) := by
    calc
      _ ≤ Lambda * (F.parameters.h t)⁻¹ *
          ((F.metric t).edist ((F.event t hT).caps i).tip (initial.chart x)).toReal := hinverse
      _ ≤ Lambda * (F.parameters.h t)⁻¹ *
          (F.parameters.h t * (F.standard_initial.cylindrical_end.radius + 5 +
            Real.sqrt (1 + old.epsilon) * |c|)) :=
        mul_le_mul_of_nonneg_left hphysicalReal
          (mul_nonneg hLambdaPos.le (inv_pos.mpr hh).le)
      _ = Lambda * (g0.cylindrical_end.radius + 5 + Real.sqrt (1 + old.epsilon) * |c|) := by
        rw [hrad]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul hsqrt habs (abs_nonneg c) hLambdaPos.le) _)
        hLambdaPos.le
  exact (not_lt_of_ge (hfarReal.trans hupper)) hgap

end PoincareConjecture.M47
