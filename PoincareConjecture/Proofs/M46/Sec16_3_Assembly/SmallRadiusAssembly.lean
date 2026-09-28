import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.LowScalarCylinder
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_CanonicalVolume









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M46



def RegularSourceProducer {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (rNext cutoff rho taubar l0 V : ℝ) : Prop :=
  ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
    ObservedInputs p rNext cutoff F O →
    ∀ D : NoncollapseTest F O, surgeryEpochStart p.i ≤ D.time →
      (F.connection D.time).scalarCurvature D.center < rNext⁻¹ ^ 2 →
      rho ≤ D.radius →
      ∃ H : HalfRadiusHistory D, Nonempty (StableSource H taubar l0 V)



def LowScalarCylinderProducer {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (rNext cutoff rho : ℝ) : Prop :=
  ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
    ObservedInputs p rNext cutoff F O →
    ∀ D : NoncollapseTest F O, surgeryEpochStart p.i ≤ D.time →
      (F.connection D.time).scalarCurvature D.center < rNext⁻¹ ^ 2 →
      Nonempty (LowScalarCylinder D rho)



theorem testConclusion_of_regularSource_and_cylinder (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    {rNext cutoff rho : ℝ} (hrNext : 0 < rNext)
    (hrLast : rNext ≤ p.r (Fin.last p.i)) (hrho : 0 < rho) (hrho_le : rho ≤ rNext)
    (regular : RegularSourceProducer.{u} p rNext cutoff rho taubar l0 V)
    (cylinders : LowScalarCylinderProducer.{u} p rNext cutoff rho)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O) (D : NoncollapseTest F O)
    (hnew : surgeryEpochStart p.i ≤ D.time) :
    TestConclusion p
      (smallRadiusUniformData p U (canonicalVolumeConstant p) (canonicalVolumeConstant_pos p))
      rNext rho D := by
  by_cases hhigh : rNext⁻¹ ^ 2 ≤ (F.connection D.time).scalarCurvature D.center
  · refine Or.inl ⟨hhigh, ?_⟩
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (smallRadiusUniformData_le_canonical p U _ _) (pow_nonneg D.radius_pos.le 3))).trans
      (canonical_test_volume P p hrNext hrLast inputs D hhigh)
  have hlow := lt_of_not_ge hhigh
  by_cases hlarge : rho ≤ D.radius
  · exact Or.inr (Or.inr (regular F O inputs D hnew hlow hlarge))
  obtain ⟨C⟩ := cylinders F O inputs D hnew hlow
  have hepsilon : rho ≤ F.parameters.epsilon := by
    rw [inputs.old.epsilon_eq]
    exact hrho_le.trans (hrLast.trans (p.r_le_epsilon _))
  obtain ⟨H, source⟩ := regular F O inputs (C.test hrho hepsilon) hnew hlow le_rfl
  obtain ⟨source⟩ := source
  refine Or.inr (Or.inl ⟨hlow, lt_of_not_ge hlarge, ?_⟩)
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (smallRadiusUniformData_le_small_ball p U _ _) (pow_nonneg D.radius_pos.le 3))).trans
      (C.small_volume P p U hrho hepsilon (le_of_not_ge hlarge) source)




theorem induction_of_regular_sources_and_cylinders (P : M46Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (produce : ∀ (p : SurgeryParameterPrefix S.constants), S.SeedCompatible p →
      ∃ taubar l0 V : ℝ, ∃ _U : M15GeneralizedUniformData.{u} 3 taubar l0 V,
        ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
          ∃ rho : ℝ, 0 < rho ∧ rho ≤ rNext ∧
          ∃ delta : ℝ, 0 < delta ∧ delta ≤ p.Delta (Fin.last p.i) ∧
            RegularSourceProducer.{u} p rNext delta rho taubar l0 V ∧
            LowScalarCylinderProducer.{u} p rNext delta rho) :
    Nonempty (RepairedNoncollapseInductionData.{u} S) := by
  apply induction_of_uniform_sources P S
  intro p hp
  obtain ⟨taubar, l0, V, U, hU⟩ := produce p hp
  refine ⟨taubar, l0, V,
    smallRadiusUniformData p U (canonicalVolumeConstant p) (canonicalVolumeConstant_pos p), ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨rho, hrho, hrho_le, delta, hdelta, hdelta_le, regular, cylinders⟩ :=
    hU rNext hrNext hrLast
  refine ⟨rho, hrho, hrho_le, delta, hdelta, hdelta_le, ?_⟩
  intro F O inputs D hnew
  exact testConclusion_of_regularSource_and_cylinder P p U hrNext hrLast hrho hrho_le
    regular cylinders inputs D hnew

end PoincareConjecture.Proofs.M46
