import PoincareConjecture.Proofs.M35.CapGeometry.CanonicalTimeAssembly
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.BoundedTipThreshold
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.SelectedCapAssembly
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.SelectedCollars

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open OrdinaryRealization

theorem standard_cap_canonical
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (epsilon : ℝ)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        StandardCanonicalAlternative E.atlas E.flow t x epsilon C := by
  apply canonical_of_bounded_tip_caps P E epsilon he hehalf
  intro D hD
  apply exists_bounded_tip_cap_threshold_of_selected P E epsilon D
  intro t x ht hR hd L kappa A
  obtain ⟨s, _F, hs, _hF, hcollars⟩ :=
    blowupSequence_bounded_tip_radial_collars P E t x ht hR L A he hehalf hD hd
  exact blowupSequence_caps_of_radial_collars P E t x ht hR L A he hehalf hD hd hs hcollars

end PoincareConjecture.M35.Uniqueness
