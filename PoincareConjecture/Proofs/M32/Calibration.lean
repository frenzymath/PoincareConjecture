import PoincareConjecture.Proofs.M31
import PoincareConjecture.Proofs.M32.Providers











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem m31M32UniformCalibration
    (L31 : RepairedSingularRegularLimitTheory.{u})
    (L32 : RepairedHornSelectionTheory.{u})
    (A : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ terminalAccuracyFactor * epsilon₀ ≤ A.epsilon₀ ∧
      (∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ},
        ∀ H : SingularTimeAssumptions F T M,
          H.epsilon ≤ epsilon₀ → Nonempty (RepairedSingularRegularLimitData H)) ∧
      (∀ epsilon C analyticConstant : ℝ,
        0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → 0 < analyticConstant →
        Nonempty (M32DeepHornScaleSelection.{u} epsilon C analyticConstant)) := by
  obtain ⟨e31, he31, hA, limit⟩ := L31.limit A
  obtain ⟨e32, he32, _, selector⟩ := L32.scale_selection
  refine ⟨min e31 e32, lt_min he31 he32, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (min_le_left e31 e32)
      terminalAccuracyFactor_pos.le).trans hA
  · intro M _ _ _ _ _ _ _ _ F T H he
    exact limit H (he.trans (min_le_left e31 e32))
  · intro epsilon C analyticConstant he he0 hC hAnalytic
    apply selector epsilon C analyticConstant he
      (he0.trans (min_le_right e31 e32)) hC hAnalytic A
    exact (mul_le_mul_of_nonneg_left
      (he0.trans (min_le_left e31 e32)) terminalAccuracyFactor_pos.le).trans hA



theorem m31M32CalibrationFromMilestones
    (A : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ terminalAccuracyFactor * epsilon₀ ≤ A.epsilon₀ ∧
      (∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ},
        ∀ H : SingularTimeAssumptions F T M,
          H.epsilon ≤ epsilon₀ → Nonempty (RepairedSingularRegularLimitData H)) ∧
      (∀ epsilon C analyticConstant : ℝ,
        0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → 0 < analyticConstant →
        Nonempty (M32DeepHornScaleSelection.{u} epsilon C analyticConstant)) :=
  m31M32UniformCalibration m31SingularRegularLimitTheory m32HornSelectionFromMilestones A



noncomputable def M32DeepHornScaleSelection.restrictHeight
    {epsilon C analyticConstant : ℝ}
    (S : M32DeepHornScaleSelection.{u} epsilon C analyticConstant)
    (factor bound : ℝ) (hfactor : 0 < factor) (hbound : 0 < bound) :
    M32DeepHornScaleSelection.{u} epsilon C analyticConstant where
  h := fun rho delta => min (S.h rho delta) (min (factor * rho) bound)
  h_pos := fun rho delta hr hd =>
    lt_min (S.h_pos rho delta hr hd) (lt_min (mul_pos hfactor hr) hbound)
  h_le := fun rho delta hr hd =>
    (min_le_left _ _).trans (S.h_le rho delta hr hd)
  h_mono_rho := by
    intro delta hd rho hr rho' hr' hle
    exact min_le_min (S.h_mono_rho delta hd hr hr' hle)
      (min_le_min (mul_le_mul_of_nonneg_left hle hfactor.le) le_rfl)
  h_mono_delta := by
    intro rho hr delta hd delta' hd' hle
    exact min_le_min (S.h_mono_delta rho hr hd hd' hle) le_rfl
  h_upper := fun rho delta hr hd =>
    (min_le_left _ _).trans (S.h_upper rho delta hr hd)
  deep_horn := by
    intro rho delta a hr hd ha hle
    exact S.deep_horn rho delta a hr hd ha (hle.trans (min_le_left _ _))


theorem M32DeepHornScaleSelection.restrictHeight_le_radius
    {epsilon C analyticConstant : ℝ}
    (S : M32DeepHornScaleSelection.{u} epsilon C analyticConstant)
    (factor bound : ℝ) (hfactor : 0 < factor) (hbound : 0 < bound)
    (rho delta : ℝ) :
    (S.restrictHeight factor bound hfactor hbound).h rho delta ≤ factor * rho :=
  (min_le_right _ _).trans (min_le_left _ _)


theorem M32DeepHornScaleSelection.restrictHeight_le_bound
    {epsilon C analyticConstant : ℝ}
    (S : M32DeepHornScaleSelection.{u} epsilon C analyticConstant)
    (factor bound : ℝ) (hfactor : 0 < factor) (hbound : 0 < bound)
    (rho delta : ℝ) :
    (S.restrictHeight factor bound hfactor hbound).h rho delta ≤ bound :=
  (min_le_right _ _).trans (min_le_right _ _)

end PoincareConjecture
