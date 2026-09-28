import PoincareConjecture.Proofs.M38.SphereBundleHeight
import PoincareConjecture.Proofs.M38.RegularClock
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.ProperControl

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M38

theorem exists_sphereBundle_pullback_flow (Q : GeneralizedSliceCarrier)
    [CompactSpace Q.carrier] (B : SurgerySphereBundle Q) :
    let A := circlePullbackCarrier Q B.projection B.projection_smooth
    let h := circlePullbackHeight Q B.projection B.projection_smooth
    ∃ Φ : ℝ → A.carrier → A.carrier,
      (∀ a, Φ 0 a = a) ∧
      (∀ s t a, Φ (s + t) a = Φ s (Φ t a)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (Function.uncurry Φ) ∧
      ∀ t a, h (Φ t a) = h a + t := by
  let A := circlePullbackCarrier Q B.projection B.projection_smooth
  let h := circlePullbackHeight Q B.projection B.projection_smooth
  have hs := circlePullback_height_smooth Q B.projection B.projection_smooth
  obtain ⟨X, hX, hclock⟩ := exists_smooth_unit_clock A h hs
    (sphereBundle_pullback_height_regular Q B)
  obtain ⟨Φ, hi, _, ha, hΦ, hh⟩ :=
    Poincare.Manifold.exists_smooth_globalFlow_of_proper_clock hs
      (CirclePullback.height_isProperMap B.projection B.projection_continuous) hX hclock
  exact ⟨Φ, hi, ha, hΦ, hh⟩

end PoincareConjecture.M38
