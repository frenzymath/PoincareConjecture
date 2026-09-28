import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.PointwiseTerminalAlternative
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedConclusion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m65Family_pointwise_terminal_alternative_proved
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u})
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}
    (compact : IsCompact (univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (E : M64AppliedFamilyEstimates V.flow.geometry C)
    (hab : a < b) {eta : ℝ} (heta : 0 < eta) :
    ∃ T : ℝ, a ≤ T ∧ T < b ∧
      Real.exp (V.flow.geometry.K2 * (b - T)) < 4 / 3 ∧
      ∀ z : LoopTwoSphere, ∃ cutoff : ℝ, 0 < cutoff ∧
        ∀ circumference (h : 0 < circumference), circumference < 1 → circumference < cutoff →
          fillingArea (F.metric b)
              ((C.solutions circumference h).projected ⟨b, hab.le, le_rfl⟩ z) ≤
            areaComparisonProfile F (fillingArea (F.metric a) (C.approximation.family z)) b +
              eta / 2 ∨
            ∀ t ∈ Icc T b, m62Length (V.flow.geometry.product circumference h).flow
              ((C.solutions circumference h).curve z) t < eta / 2 := by
  let : CompactSpace M := ⟨compact⟩
  exact m65Family_pointwise_terminal_alternative hM61 hM64 compact V C E
    (m65ImmersedFillingAreaComparison_proved F V) hab heta

end PoincareConjecture
