import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.TerminalCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})

theorem terminalNeckToOld_coordinateMap {t ε : ℝ}
    (ht : t ∈ Ico H.reference.tMinus T) (N : GeneralizedStrongNeck F t ε)
    (x₀ : H.regularRegion P04)
    (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    H.terminalNeckToOld P04 ht (H.terminalNeckCoordinateMap P04 ht N x₀ z) =
      N.coordinate_map z := by
  apply H.terminalNeckToOld_fromOld P04 ht x₀
  apply hcapture
  exact N.coordinate_map_eq (z.1, ⟨z.2, hz⟩) ▸ (N.coordinate (z.1, ⟨z.2, hz⟩)).property

variable (hΩ : H.reference.regularLimitSet.Nonempty)
  {t : ℝ} (ht : t ∈ Ioo H.reference.tMinus T)
  (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04)
  (hR : (F.connection t).scalarCurvature N.center <
    (H.terminalConnection P04).scalarCurvature x₀)
  {δ : ℝ} (hεδ : H.epsilon ≤ δ)

def regularNeckWeakenedTerminalCylinder :
    GeneralizedFlowCylinder (H.nonemptyExtension P04 hΩ).extended
      ((H.nonemptyExtension P04 hΩ).extended.slice T)
      T ((H.terminalConnection P04).scalarCurvature x₀) (Ioc (-1) 0)
      (H.terminalNeckCarrier P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ)) :=
  (H.regularNeckTerminalCylinder P04 hΩ ht N x₀ hR).restrictSpace
    (fun _ hx => N.restrictAccuracy_carrier_subset hεδ hx)

theorem regularNeckWeakenedTerminalCylinder_identity
    (h : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0)
    (x : ((H.nonemptyExtension P04 hΩ).extended.slice T).carrier) :
    (H.regularNeckWeakenedTerminalCylinder P04 hΩ ht N x₀ hR hεδ).pointMap 0 h x =
      (⟨T, x⟩ : (H.nonemptyExtension P04 hΩ).extended.point) :=
  H.regularNeckTerminalCylinder_identity P04 hΩ ht N x₀ hR h x

theorem regularNeckWeakenedTerminalCylinder_pullbackInner
    (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (x : ((H.nonemptyExtension P04 hΩ).extended.slice T).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (H.regularNeckWeakenedTerminalCylinder P04 hΩ ht N x₀ hR hεδ).pullbackInner s hs x v w =
      (H.regularNeckTerminalCylinder P04 hΩ ht N x₀ hR).pullbackInner s hs x v w := rfl

end PoincareConjecture.SingularTimeAssumptions
