import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.GluingMap



set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminalGluingMap_vertical_compatibility
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hΩ : H.reference.regularLimitSet.Nonempty)
    (t : ℝ) (_ht : t ∈ Ioc H.reference.tMinus T)
    (x : ((H.nonemptyExtension P04 hΩ).extended.slice T).carrier) :
    ∃ b, ∃ y : ((H.nonemptyExtension P04 hΩ).extended.box b).carrier.carrier,
      ∃ δ : ℝ, 0 < δ ∧
        ∀ s hs, |s - t| < δ →
          ∃ hb : s ∈ ((H.nonemptyExtension P04 hΩ).extended.box b).interval,
            H.terminalGluingMap P04 (⟨s, hs⟩, x) =
              (⟨s, ((H.nonemptyExtension P04 hΩ).extended.box b).forward s hb y⟩ :
                (H.nonemptyExtension P04 hΩ).extended.point) := by
  refine ⟨.inr PUnit.unit, H.terminalSliceHomeomorph P04 x, 1, by norm_num, ?_⟩
  intro s hs _
  exact ⟨hs, (H.regularBox_spacetime_forward P04 hΩ
    (⟨s, hs⟩, H.terminalSliceHomeomorph P04 x)).symm⟩

end PoincareConjecture.SingularTimeAssumptions
