import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.NetAssembly
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.PointwiseConclusion









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture





theorem m65CommonTerminalAlternative_proved
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u})
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}
    (compact : IsCompact (univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (E : M64AppliedFamilyEstimates V.flow.geometry C)
    (hab : a < b) {eta : ℝ} (heta : 0 < eta) :
    ∃ circumference : ℝ, ∃ h : 0 < circumference, circumference < 1 ∧
      ∀ z : LoopTwoSphere,
        freeLoopLength (F.metric b)
            ((C.solutions circumference h).projected ⟨b, hab.le, le_rfl⟩ z) < eta ∨
          fillingArea (F.metric b)
              ((C.solutions circumference h).projected ⟨b, hab.le, le_rfl⟩ z) ≤
            areaComparisonProfile F (fillingArea (F.metric a) (C.approximation.family z)) b +
              eta := by
  obtain ⟨s, has, hsb, hgrowth, pointwise⟩ :=
    m65Family_pointwise_terminal_alternative_proved hM61 hM64 compact V C E hab heta
  exact m65CommonTerminalAlternative hM64 compact V C E heta has hsb hgrowth pointwise

end PoincareConjecture
