import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Models
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Quotient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Smooth












noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]







def GlobalSplittingObligation
    (S : GradientShrinkingSolitonData 3 M)
    (G : ShrinkingSolitonFlow S) : Prop :=
  Nonempty (SphereLineProductCertificate G) ∨
    Nonempty (QuotientSphereLineCertificate G)

theorem global_model_of_splitting_obligation
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (h : GlobalSplittingObligation S G) :
    Nonempty (ThreeDimensionalSolitonModel S G) := by
  rcases h with ⟨⟨hproduct⟩⟩ | ⟨⟨hquotient⟩⟩
  · exact ⟨.sphereLine hproduct⟩
  · exact ⟨.quotientSphereLine hquotient⟩

theorem global_conclusion_of_splitting_obligation
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (h : GlobalSplittingObligation S G) :
    Nonempty (ThreeDimensionalSolitonConclusion S) := by
  obtain ⟨model⟩ := global_model_of_splitting_obligation h
  exact ⟨{ flow := G, model := model }⟩

end PoincareConjecture
