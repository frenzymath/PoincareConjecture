import PoincareConjecture.Statements.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M30.Thm11_1.BoundedDistance
import PoincareConjecture.Proofs.M30.Thm11_8.LongConclusionAssembly
import PoincareConjecture.Proofs.M30.Thm11_8.LongSlabService
import PoincareConjecture.Proofs.M30.Thm11_8.LongLimitCertificates
import PoincareConjecture.Proofs.M30.Generalized.BlowupSubsequence
import PoincareConjecture.Statements.M30Providers

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

structure M30LongContractService : Prop where
  slab : ∃ epsilonLong : ℝ, 0 < epsilonLong ∧
    ∀ (S : GeneralizedBlowupSequence.{u})
      (epsilon C kappa r₀ mu : ℝ) (T₀ : ℝ≥0∞),
      epsilon ≤ epsilonLong →
      M30LongBlowupControls S epsilon C kappa r₀ mu T₀ →
      GeneralizedBlowupBoundedDistance S →
      ∃ phi : ℕ → ℕ, ∃ hphi : StrictMono phi,
        M30LongSlabControlService (reindexedBlowupSequence S phi hphi) kappa r₀ T₀
  certificates : ∀ (S : GeneralizedBlowupSequence.{u})
    (kappa r₀ : ℝ) (T₀ : ℝ≥0∞),
    0 < r₀ →
    GeneralizedBlowupBoundedDistance S →
    M30LongSlabControlService S kappa r₀ T₀ →
    (∀ L : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀),
      M30LimitNoncollapsedAtScale L.limit kappa r₀) ∧
    (∀ (L : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀))
      (h : T₀ = ⊤), BlowupLimitNoncollapsed (h ▸ L.limit) kappa)

theorem exists_longLimitStatement_of_controlService
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (Hservice : M30LongContractService.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      M30LongLimitStatement.{u} epsilon₀ := by
  obtain ⟨epsilon29, hepsilon29, hepsilon29_le, hbound⟩ :=
    exists_boundedDistance_threshold P
  obtain ⟨epsilonLong, hepsilonLong, hslab⟩ := Hservice.slab
  refine ⟨min epsilon29 epsilonLong, lt_min hepsilon29 hepsilonLong,
    (min_le_left _ _).trans hepsilon29_le, ?_⟩
  intro S epsilon C kappa r₀ mu T₀ hepsilon H
  have hboundS := hbound S epsilon C kappa r₀ mu
    (hepsilon.trans (min_le_left _ _)) H.toM30CommonBlowupControls
  obtain ⟨phi, hphi, Hslab⟩ := hslab S epsilon C kappa r₀ mu T₀
    (hepsilon.trans (min_le_right _ _)) H hboundS
  have hboundSelected := reindexed_boundedDistance hboundS phi hphi
  obtain ⟨hnoncollapsed, hall⟩ := Hservice.certificates
    (reindexedBlowupSequence S phi hphi) kappa r₀ T₀ H.radius_pos
    hboundSelected Hslab
  obtain ⟨L⟩ := exists_repaired_long_conclusion_of_controls P hMixed hFlow hSlice
    (reindexedBlowupSequence S phi hphi) (reindexedLongBlowupControls H phi hphi)
    hboundSelected Hslab hnoncollapsed hall
  exact ⟨longConclusionOfReindexed L⟩

end PoincareConjecture.M30
