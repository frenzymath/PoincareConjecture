import PoincareConjecture.Proofs.M06
import PoincareConjecture.Proofs.M35.Prop12_31.InitialScalarFloor
import PoincareConjecture.Proofs.M35.Prop12_31.CurvatureOperator

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RepairedStandardCapExistenceData

theorem time_mul_scalar_le
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (ht : t < 1) (x : StandardCapSpace) :
    (E.flow.connection s).scalarCurvature x * s ≤
      (E.flow.connection t).scalarCurvature x * t := by
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ico 0 E.flow.base.lifetime := by
    intro u hu
    exact ⟨hu.1.le, E.lifetime_one.symm ▸ hu.2⟩
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow E.flow.base.flow hsub
    ordConnected_Ioo ⟨1 / 3, by norm_num, 2 / 3, by norm_num, by norm_num⟩
  have hcomplete (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : MetricComplete (F.metric u) :=
    E.complete u (hsub hu)
  have hoperator (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) (y : StandardCapSpace) :
      (F.connection u).NonnegativeCurvatureOperator y :=
    (F.connection u).nonnegativeCurvatureOperator_of_nonnegative_sectional_three
      (P.tensor_calculus 3 StandardCapSpace _ _) y (E.nonnegative_sectional u (hsub hu) y)
  have hbounded (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ y : StandardCapSpace,
        (F.connection u).CurvatureOperatorBound K y := by
    obtain ⟨K, hK, hb⟩ := E.flow.base.curvature_locally_bounded u hu.1.le (hsub hu).2
    refine ⟨K, hK, fun y => ?_⟩
    exact (F.connection u).curvatureOperatorBound_of_curvatureTensorNorm_le y
      ((le_abs_self _).trans (hb u ⟨hu.1.le, le_rfl⟩ y))
  have h := (differentialHarnackAncientTheory P).finite_integrated
    3 StandardCapSpace 0 1 s t hs hst ht F hcomplete hoperator hbounded
    (fun _ => x) contMDiffOn_const x x rfl rfl
  have henergy : spacetimeEnergy F (fun _ => x) s t = 0 := by
    unfold spacetimeEnergy
    simp only [mfderiv_const, zero_apply, map_zero,
      intervalIntegral.integral_zero]
  change (F.connection s).scalarCurvature x * s ≤ (F.connection t).scalarCurvature x * t
  simpa only [henergy, zero_div, neg_zero, Real.exp_zero, mul_one, sub_zero] using h

theorem exists_scalar_floor
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) :
    ∃ b : ℝ, 0 < b ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
      b ≤ (E.flow.connection t).scalarCurvature x := by
  obtain ⟨δ, B, hδ, hδhalf, hB, hearly⟩ := E.exists_initial_scalar_floor P
  refine ⟨δ * B, mul_pos hδ hB, ?_⟩
  intro t ht x
  have ht1 : t < 1 := E.lifetime_one ▸ ht.2
  by_cases htd : t ≤ δ
  · have h := hearly t ⟨ht.1, htd⟩ x
    have hδ1 : δ ≤ 1 := by linarith
    exact (mul_le_of_le_one_left hB.le hδ1).trans h
  · have hdt : δ < t := lt_of_not_ge htd
    have h := E.time_mul_scalar_le P hδ hdt ht1 x
    have hb := hearly δ ⟨hδ.le, le_rfl⟩ x
    have hpos : 0 < (E.flow.connection t).scalarCurvature x := by
      have hleft : 0 < (E.flow.connection δ).scalarCurvature x * δ :=
        mul_pos (hB.trans_le hb) hδ
      exact pos_of_mul_pos_left (hleft.trans_le h) (hδ.trans hdt).le
    calc
      δ * B ≤ (E.flow.connection δ).scalarCurvature x * δ := by nlinarith
      _ ≤ (E.flow.connection t).scalarCurvature x * t := h
      _ ≤ (E.flow.connection t).scalarCurvature x := mul_le_of_le_one_right hpos.le ht1.le

end PoincareConjecture.RepairedStandardCapExistenceData
