import PoincareConjecture.Proofs.M47.PositiveGradientSpatial
import PoincareConjecture.Proofs.M47.PositiveGradientCurvature
import PoincareConjecture.Proofs.M47.ComponentEstimateMinimum
import PoincareConjecture.Statements.M47PositiveComponent

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

theorem positive_component_blowup (hC : RicciFlowCurvatureTheory.{u}) :
    M47PositiveComponentBlowupStatement.{u} := by
  intro M _ _ _ _ _ _ _ T hT F hpos hblow L
  obtain ⟨B, _, huniform⟩ :=
    exists_scalar_maximum_uniformization_threshold hC hT F hpos
  obtain ⟨s, hs, p, hp⟩ := hblow (max B (2 * max L 0)) 0 hT
  have hs0 : 0 < s := by simpa only [max_self] using hs.1
  have hsI : s ∈ Ico 0 T := ⟨hs0.le, hs.2⟩
  have hcurv := curvature_norm_le_scalar_on_positive_flow hC hT F hpos s hsI p
  have hcont :=
    (hC.tensor_calculus 3 M (F.metric s) (F.connection s)).contMDiff_scalarCurvature.continuous
  obtain ⟨q, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (univ_nonempty : (univ : Set M).Nonempty) hcont.continuousOn
  have hlarge : max B (2 * max L 0) < (F.connection s).scalarCurvature q :=
    hp.trans_le (hcurv.trans (hmax (mem_univ p)))
  have hB : B ≤ (F.connection s).scalarCurvature q :=
    (le_max_left _ _).trans hlarge.le
  have hL : L ≤ (F.connection s).scalarCurvature q / 2 := by
    have h := (le_max_right _ _).trans hlarge.le
    have hL0 := le_max_left L 0
    linarith only [h, hL0]
  have hinit : ∀ x ∈ (univ : Set M), L ≤ (F.connection s).scalarCurvature x := by
    intro x _
    exact hL.trans (huniform s hsI q hB (fun y => hmax (mem_univ y)) x)
  let P : M47ScalarPersistencePredecessors.{u} :=
    { tensor_calculus := fun M _ _ _ => hC.tensor_calculus 3 M
      scalar_regular := fun M _ _ _ => hC.scalar_regular 3 M
      scalar_evolution := fun M _ _ _ => hC.scalar_evolution 3 M }
  refine ⟨s, hs0.le, hs.2, ?_⟩
  intro t ht x
  have hJ : Icc s t ⊆ Ico 0 T := by
    intro r hr
    exact ⟨hs0.le.trans hr.1, hr.2.trans_lt ht.2⟩
  exact M47.component_scalar_floor_preserved P F isCompact_univ isOpen_univ ht.1.le hJ
    hinit t ⟨ht.1.le, le_rfl⟩ x (mem_univ x)

end PoincareConjecture.M47Positive
