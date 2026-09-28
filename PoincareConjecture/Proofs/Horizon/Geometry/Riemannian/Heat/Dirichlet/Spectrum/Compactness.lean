import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.EnergyFlow
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralCompactness

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable (D : LeviCivitaData g) (Ω : Set M) (hn : 0 < n)
  (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))

include hn hΩ hc

theorem countable_eigenIndex : Countable (EigenIndex D Ω) :=
  Poincare.Analysis.Dirichlet.CompactSpectral.countable_basisIndex
    (domainL2Resolvent D Ω) (isCompactOperator_domainL2Resolvent D Ω hn hΩ hc)
    domainL2Resolvent_isSelfAdjoint

theorem finite_eigenvalue_le (R : ℝ) :
    Set.Finite {i : EigenIndex D Ω | eigenvalue D Ω i ≤ R} := by
  have h := Poincare.Analysis.Dirichlet.CompactSpectral.finite_transformed_rate_le_of_nonneg
    (domainL2Resolvent D Ω) (isCompactOperator_domainL2Resolvent D Ω hn hΩ hc)
    domainL2Resolvent_isSelfAdjoint
    (fun f => by rw [domainL2Resolvent_inner]; exact real_inner_self_nonneg)
    (R := max R 0) (le_max_right _ _)
  apply h.subset
  intro i hi
  change eigenvalue D Ω i ≤ max R 0
  exact hi.trans (le_max_left _ _)

theorem heatSemigroup_eq_energy_comp {t : ℝ≥0} (ht : 0 < t) :
    heatSemigroup D Ω hn hΩ hc t = (toDomainL2 D Ω).comp
      (energyHeatSpectralPower D Ω hn hΩ hc 0 (t : ℝ)) := by
  ext f
  have ht' : 0 < (t : ℝ) := ht
  rw [ContinuousLinearMap.comp_apply,
    toDomainL2_energyHeatSpectralPower D Ω hn hΩ hc 0 ht',
    heatSpectralPower_zero_eq_heatSemigroup D Ω hn hΩ hc ht']
  simp

theorem isCompactOperator_heatSemigroup {t : ℝ≥0} (ht : 0 < t) :
    IsCompactOperator (heatSemigroup D Ω hn hΩ hc t) := by
  rw [heatSemigroup_eq_energy_comp D Ω hn hΩ hc ht]
  exact (isCompactOperator_toDomainL2 D Ω hn hΩ hc).comp_clm
    (energyHeatSpectralPower D Ω hn hΩ hc 0 (t : ℝ))

end PoincareConjecture.LeviCivitaData.Dirichlet
