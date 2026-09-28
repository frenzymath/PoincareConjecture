import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedLimitNoncollapse
import PoincareConjecture.Definitions.M30ControlledBlowupLimits










set_option autoImplicit false

open scoped ENNReal

universe u

namespace PoincareConjecture.M30



theorem long_limit_certificates_of_longSlabService
    (S : GeneralizedBlowupSequence.{u}) {T0 : ℝ≥0∞} {kappa r0 : ℝ}
    (hr0 : 0 < r0) (H : M30LongSlabControlService S kappa r0 T0) :
    (∀ G : GeneralizedBlowupConvergence S (blowupBackwardInterval T0),
      M30LimitNoncollapsedAtScale G.limit kappa r0) ∧
    (∀ (G : GeneralizedBlowupConvergence S (blowupBackwardInterval T0))
      (h : T0 = ⊤), BlowupLimitNoncollapsed (h ▸ G.limit) kappa) := by
  constructor
  · intro G t ht p r hr _hcutoff htime hcurv
    exact generalized_limit_noncollapsed_of_longSlabService G H hr0 t ht p r hr htime hcurv
  · intro G h
    subst h
    exact generalized_limit_noncollapsed_of_longSlabService G H hr0

end PoincareConjecture.M30
