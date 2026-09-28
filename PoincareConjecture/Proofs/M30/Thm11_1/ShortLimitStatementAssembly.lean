import PoincareConjecture.Statements.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M30.Thm11_1.BoundedDistance
import PoincareConjecture.Proofs.M30.Thm11_1.ShortControlsAssembly
import PoincareConjecture.Proofs.M30.Generalized.BlowupSubsequence
import PoincareConjecture.Statements.M30Providers











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30




def M30ShortControlService : Prop :=
  ∃ epsilonShort : ℝ, 0 < epsilonShort ∧
    ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C kappa r₀ mu : ℝ),
      epsilon ≤ epsilonShort →
      M30CommonBlowupControls S epsilon C kappa r₀ mu →
      GeneralizedBlowupBoundedDistance S →
      ∃ phi : ℕ → ℕ, ∃ hphi : StrictMono phi,
        Nonempty (ShortControlledBlowupHypotheses
          (reindexedBlowupSequence S phi hphi) kappa r₀)




theorem exists_shortLimitStatement_of_controlService
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (hshort : M30ShortControlService.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      M30ShortLimitStatement.{u} epsilon₀ := by
  obtain ⟨epsilon29, hepsilon29, hepsilon29_le, hbound⟩ :=
    exists_boundedDistance_threshold P
  obtain ⟨epsilonShort, hepsilonShort, hshort⟩ := hshort
  refine ⟨min epsilon29 epsilonShort, lt_min hepsilon29 hepsilonShort,
    (min_le_left _ _).trans hepsilon29_le, ?_⟩
  intro S epsilon C kappa r₀ mu hepsilon H
  have hboundS := hbound S epsilon C kappa r₀ mu
    (hepsilon.trans (min_le_left _ _)) H
  obtain ⟨phi, hphi, Hshort⟩ := hshort S epsilon C kappa r₀ mu
    (hepsilon.trans (min_le_right _ _)) H hboundS
  obtain ⟨Hshort⟩ := Hshort
  exact shortConclusion_of_reindexed
    (exists_repaired_short_conclusion_of_controls P hMixed hFlow hSlice
      (reindexedBlowupSequence S phi hphi) (reindexedCommonBlowupControls H phi hphi)
      (reindexed_boundedDistance hboundS phi hphi) Hshort)

end PoincareConjecture.M30
