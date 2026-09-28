import PoincareConjecture.Proofs.M30.Thm11_8.RawFiniteScalarBound
import PoincareConjecture.Proofs.M30.Thm11_8.BoundedFiniteContinuation
import PoincareConjecture.Proofs.M30.Thm11_8.CofinalFiniteLimitClosure
import PoincareConjecture.Proofs.M30.Thm11_8.LongSlabServiceFromConvergence
import PoincareConjecture.Proofs.M30.Thm11_8.LongLimitStatementAssembly
import PoincareConjecture.Proofs.M30.Thm11_1.ShortControlSupplier













set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture.M30




theorem exists_raw_long_convergence_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (S : GeneralizedBlowupSequence.{u})
        (epsilon C kappa r0 mu : ℝ) (T0 : ℝ≥0∞),
        epsilon ≤ epsilon0 →
        M30LongBlowupControls S epsilon C kappa r0 mu T0 →
        GeneralizedBlowupBoundedDistance S →
        Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T0)) := by
  obtain ⟨epsilonFinite, hfinitePos, hfiniteSmall, hfinite⟩ :=
    exists_raw_finite_scalar_bound_threshold P
  obtain ⟨epsilonShort, hshortPos, hshort⟩ := shortControlService P.m04
  refine ⟨min epsilonFinite epsilonShort, lt_min hfinitePos hshortPos,
    (min_le_left _ _).trans hfiniteSmall, ?_⟩
  intro S epsilon C kappa r0 mu T0 hepsilon H hbound
  obtain ⟨phi, hphi, ⟨Hshort⟩⟩ := hshort S epsilon C kappa r0 mu
    (hepsilon.trans (min_le_right _ _)) H.toM30CommonBlowupControls hbound
  let S' := reindexedBlowupSequence S phi hphi
  let H' := reindexedLongBlowupControls H phi hphi
  have hbound' := reindexed_boundedDistance hbound phi hphi
  obtain ⟨G⟩ := exists_backward_convergence_of_finite_extension P H' Hshort hbound'
    (by
      intro T hT hTT0 G
      exact exists_larger_finite_convergence_of_scalar_bound P H' hbound' G hT hTT0
        (hfinite S' epsilon C kappa r0 mu
          (hepsilon.trans (min_le_left _ _)) T0 H' T hT hTT0 G))
  exact ⟨convergenceOfReindexed G⟩



theorem longContractService (P : M30ControlledBlowupPredecessors.{u}) :
    M30LongContractService.{u} := by
  obtain ⟨epsilon0, hepsilon0, _hsmall, hconvergence⟩ :=
    exists_raw_long_convergence_threshold P
  refine {
    slab := ⟨epsilon0, hepsilon0, ?_⟩
    certificates := ?_ }
  · intro S epsilon C kappa r0 mu T0 hepsilon H hbound
    obtain ⟨G⟩ := hconvergence S epsilon C kappa r0 mu T0 hepsilon H hbound
    exact ⟨G.subsequence, G.subsequence_strictMono,
      longSlabControlService_of_convergence P.m04 H G⟩
  · intro S kappa r0 T0 hr0 _hbound H
    exact long_limit_certificates_of_longSlabService S hr0 H

end PoincareConjecture.M30
