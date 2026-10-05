import PoincareLib.Geometry.RicciFlow.Local.ExistenceUniquenessContinuation
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.PointedCompactness
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Predecessors
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Kappa
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Blowup
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Main

/-!
# Applying M35's actual earlier services

The construction uses the selected M34 existence package without choosing a
different standard flow. The seven services include the actual compact
surface uniqueness and ordinary compactness operations. The M35 proof
derives the scalar and canonical estimates from those earlier services
and supplies common-domain uniqueness using the published M34 theorem.
-/

set_option autoImplicit false

namespace PoincareMT

/-- Theorem 12.5, pp. 295-296, and Theorem 12.32, pp. 326-327:
the lower milestones supply the seven services used by M35. -/
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

/-- Theorem 12.5 and Proposition 12.31 through Theorem 12.32:
apply the complete M35 proof to the published lower-milestone services. -/
theorem m35StandardCapUniquenessFromMilestones :
    RepairedStandardCapUniquenessTheory :=
  repairedStandardCapUniqueness m35StandardCapPredecessorsFromMilestones

/-- Proposition 12.31 applied to the supplied M34 flow and connection. -/
theorem m35StandardScalarRateFromMilestones (g₀ : StandardInitialMetric)
    (E : RepairedStandardCapExistenceData g₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace, c / (1 - t) ≤ (E.flow.connection t).scalarCurvature x := by
  obtain ⟨U⟩ := m35StandardCapUniquenessFromMilestones.estimates g₀ E
  exact U.scalar_lower_bound

end PoincareMT
