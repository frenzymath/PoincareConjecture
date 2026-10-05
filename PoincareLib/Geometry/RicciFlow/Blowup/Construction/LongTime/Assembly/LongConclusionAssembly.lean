import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Theory
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.AncientIdentification
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.Assembly.LongControlsAssembly

/-!
# Packaging the long conclusion

The convergence assembly and the finite-scale noncollapse transport are
separate obligations.  These constructors package them without weakening
the frozen statement.  The second constructor also records the exact
infinite-horizon route: eliminate the equality to `⊤` before constructing the
ancient identification.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- Package a generalized convergence witness with the two remaining long
conclusion certificates. -/
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

/-- Finite-radius certificates available at every positive cutoff give the
all-scale predicate by choosing the cutoff equal to the tested radius. This
is the limit-side form of the source observation that
`r₀ * sqrt (S.scale k)` eventually exceeds every fixed normalized radius. -/
theorem blowupLimitNoncollapsed_of_all_radius_cuts
    {J : Set ℝ} (L : BlowupLimitFlow.{u} J) {kappa : ℝ}
    (hcuts : ∀ R : ℝ, 0 < R → M30LimitNoncollapsedAtScale L kappa R) :
    BlowupLimitNoncollapsed L kappa := by
  intro t ht p r hr htime hcurvature
  exact hcuts r hr t ht p r hr le_rfl htime hcurvature

/-- The all-scale noncollapse certificate supplies the ancient branch.  The
`subst` is intentional: the target is dependent on the horizon equality. -/
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

/-- A radius-cut family is enough for the infinite-horizon branch: after
eliminating the dependent horizon equality, specialize it at the radius
tested by `BlowupLimitNoncollapsed`. -/
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

/-- Combine the checked long-control convergence adapter with externally
supplied finite-scale and all-scale noncollapse certificates. -/
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

/-- Variant of the long controls adapter for a source proof that produces
finite noncollapse at every radius. The radius family is converted only at
the final limit boundary, where the tested radius is available to specialize
the finite predicate. -/
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

end PoincareMT.M30
