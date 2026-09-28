import PoincareConjecture.Statements.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M30.Thm11_8.AncientIdentification
import PoincareConjecture.Proofs.M30.Thm11_8.LongControlsAssembly











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30



theorem repairedLongConclusion_of_convergence
    (S : GeneralizedBlowupSequence.{u}) {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (hconvergence : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀))
    (hnoncollapsed : M30LimitNoncollapsedAtScale hconvergence.limit kappa r₀)
    (hancient : ∀ h : T₀ = ⊤,
      Nonempty (M30AncientKappaIdentification (h ▸ hconvergence.limit) kappa)) :
    Nonempty (RepairedLongControlledBlowupConclusion S kappa r₀ T₀) := by
  exact ⟨{
    convergence := hconvergence
    noncollapsed := hnoncollapsed
    ancient := hancient }⟩





theorem blowupLimitNoncollapsed_of_all_radius_cuts
    {J : Set ℝ} (L : BlowupLimitFlow.{u} J) {kappa : ℝ}
    (hcuts : ∀ R : ℝ, 0 < R → M30LimitNoncollapsedAtScale L kappa R) :
    BlowupLimitNoncollapsed L kappa := by
  intro t ht p r hr htime hcurvature
  exact hcuts r hr t ht p r hr le_rfl htime hcurvature



theorem repairedLongConclusion_of_allScale_noncollapsed
    (hC : RicciFlowCurvatureTheory.{u})
    (S : GeneralizedBlowupSequence.{u}) {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (hkappa : 0 < kappa)
    (hconvergence : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀))
    (hnoncollapsed : M30LimitNoncollapsedAtScale hconvergence.limit kappa r₀)
    (hall : ∀ h : T₀ = ⊤,
      BlowupLimitNoncollapsed (h ▸ hconvergence.limit) kappa) :
    Nonempty (RepairedLongControlledBlowupConclusion S kappa r₀ T₀) := by
  apply repairedLongConclusion_of_convergence S hconvergence hnoncollapsed
  intro h
  subst h
  exact ⟨ancientKappaIdentificationOfNoncollapsed hC hconvergence.limit hkappa
    (hall rfl)⟩




theorem repairedLongConclusion_of_radius_cut_family
    (hC : RicciFlowCurvatureTheory.{u})
    (S : GeneralizedBlowupSequence.{u}) {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (hkappa : 0 < kappa)
    (hconvergence : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀))
    (hnoncollapsed : M30LimitNoncollapsedAtScale hconvergence.limit kappa r₀)
    (hcuts : ∀ h : T₀ = ⊤, ∀ R : ℝ, 0 < R →
      M30LimitNoncollapsedAtScale (h ▸ hconvergence.limit) kappa R) :
    Nonempty (RepairedLongControlledBlowupConclusion S kappa r₀ T₀) := by
  apply repairedLongConclusion_of_allScale_noncollapsed hC S hkappa
    hconvergence hnoncollapsed
  intro h
  subst h
  exact blowupLimitNoncollapsed_of_all_radius_cuts _ (hcuts rfl)



theorem exists_repaired_long_conclusion_of_controls
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u})
    {epsilon canonicalConstant kappa r₀ mu : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongBlowupControls S epsilon canonicalConstant kappa r₀ mu T₀)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (Hslab : M30LongSlabControlService S kappa r₀ T₀)
    (hnoncollapsed : ∀ L : GeneralizedBlowupConvergence S
      (blowupBackwardInterval T₀),
      M30LimitNoncollapsedAtScale L.limit kappa r₀)
    (hall : ∀ (L : GeneralizedBlowupConvergence S
      (blowupBackwardInterval T₀)) (h : T₀ = ⊤),
      BlowupLimitNoncollapsed (h ▸ L.limit) kappa) :
    Nonempty (RepairedLongControlledBlowupConclusion S kappa r₀ T₀) := by
  obtain ⟨L⟩ := exists_long_generalized_convergence_of_controls
    P hMixed hFlow hSlice S H hbound Hslab
  exact repairedLongConclusion_of_allScale_noncollapsed P.m04 S H.kappa_pos L
    (hnoncollapsed L) (hall L)





theorem exists_repaired_long_conclusion_of_radius_cut_family
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u})
    {epsilon canonicalConstant kappa r₀ mu : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongBlowupControls S epsilon canonicalConstant kappa r₀ mu T₀)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (Hslab : M30LongSlabControlService S kappa r₀ T₀)
    (hnoncollapsed : ∀ L : GeneralizedBlowupConvergence S
      (blowupBackwardInterval T₀),
      M30LimitNoncollapsedAtScale L.limit kappa r₀)
    (hcuts : ∀ (L : GeneralizedBlowupConvergence S
      (blowupBackwardInterval T₀)) (h : T₀ = ⊤) (R : ℝ), 0 < R →
      M30LimitNoncollapsedAtScale (h ▸ L.limit) kappa R) :
    Nonempty (RepairedLongControlledBlowupConclusion S kappa r₀ T₀) := by
  obtain ⟨L⟩ := exists_long_generalized_convergence_of_controls
    P hMixed hFlow hSlice S H hbound Hslab
  exact repairedLongConclusion_of_radius_cut_family P.m04 S H.kappa_pos L
    (hnoncollapsed L) (hcuts L)

end PoincareConjecture.M30
