import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Models
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Quotient
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Smooth

/-!
# Assembly of the global model alternatives

The frozen model certificates contain the exact same-flow metric transport
required by the three-dimensional classification node.  The final conversion
to the existing `ThreeDimensionalSolitonModel` is fully constructive.
Existence of one of the two certificates is exposed as an explicit
obligation, so a downstream proof cannot silently assume a product or
quotient witness.  The orientation-cover and setoid-quotient constructions
remain separate inputs to the proof that discharges this obligation.
-/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- The two global model certificates that remain after the rank-one cover.

This is a proposition-valued obligation, rather than an assumed product
witness.  It records exactly which smooth and metric data a globalization
proof must construct.
-/
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

end PoincareMT
