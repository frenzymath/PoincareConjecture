import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.GeneralizedLimit.GeneralizedLimitNoncollapse
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data

/-!
# Noncollapse certificates in the long conclusion

The all-scale volume passage on the supplied limit yields the finite
cutoff certificate and the dependent infinite-horizon clause without
changing the limit. Source: Morgan--Tian Theorem 11.8, p. 272; M30
derivation `generalized-limit-noncollapse.md`.
-/

set_option autoImplicit false

open scoped ENNReal

universe u

namespace PoincareMT.M30

/-- The actual all-scale volume bound supplies both long conclusion
certificates (Theorem 11.8, p. 272), retaining the original limit. -/
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

end PoincareMT.M30
