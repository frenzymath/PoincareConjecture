import PoincareConjecture.Proofs.M03
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M07
import PoincareConjecture.Proofs.M13
import PoincareConjecture.Proofs.M27.Providers
import PoincareConjecture.Proofs.M30.Providers
import PoincareConjecture.Proofs.M35











set_option autoImplicit false

namespace PoincareConjecture



theorem m35StandardCapPredecessorsFromMilestones : M35StandardCapPredecessors := by
  obtain ⟨epsilon₀, hpos, hsmall, _short, long⟩ :=
    m30ControlledGeneralizedBlowupLimitsFromMilestones.limits
  refine {
    curvature := ricciFlowCurvatureTheory
    compact_surface_uniqueness := ?_
    pointed_compactness := fun H => pointedRicciFlowCompactness_from_M04 H
    ordinary_flow := (generalizedParabolicRescaling_from_M12 3).ordinary_flow
    metric_homothety := (generalizedParabolicRescaling_from_M12 3).metric_homothety
    kappa_models := m27KappaAlternativesFromMilestones
    long_limits := ⟨epsilon₀, hpos, hsmall, long⟩
  }
  intro M _ _ _ _ _ _
  exact (ricciFlowLocalTheory (n := 2) (M := M)).2.1



theorem m35StandardCapUniquenessFromMilestones :
    RepairedStandardCapUniquenessTheory :=
  repairedStandardCapUniqueness m35StandardCapPredecessorsFromMilestones


theorem m35StandardScalarRateFromMilestones (g₀ : StandardInitialMetric)
    (E : RepairedStandardCapExistenceData g₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace, c / (1 - t) ≤ (E.flow.connection t).scalarCurvature x := by
  obtain ⟨U⟩ := m35StandardCapUniquenessFromMilestones.estimates g₀ E
  exact U.scalar_lower_bound

end PoincareConjecture
