import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ReferenceCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Restriction

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
  {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T)

def terminalNeckToOld : (H.extendedSliceGeometry P04 T).slice.carrier → (F.slice t).carrier :=
  H.regularNeckSourceMap P04 ht ∘ H.terminalSliceHomeomorph P04

def terminalNeckFromOld (x₀ : H.regularRegion P04) :
    (F.slice t).carrier → (H.extendedSliceGeometry P04 T).slice.carrier :=
  (H.terminalSliceHomeomorph P04).symm ∘
    (SingularRegularLimit.openRetraction (H.regularRegion P04) x₀ ∘ H.reference.inverse t ht)

theorem terminalNeckToOld_openEmbedding : Topology.IsOpenEmbedding (H.terminalNeckToOld P04 ht) :=
  ((H.reference.forward_openEmbedding t ht).comp
    (H.regularRegion P04).isOpen.isOpenEmbedding_subtypeVal).comp
      (H.terminalSliceHomeomorph P04).isOpenEmbedding

theorem terminalNeckToOld_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ (H.terminalNeckToOld P04 ht) :=
  ((H.reference.forward_smooth t ht).comp contMDiff_subtype_val).comp
    (H.terminalSliceHomeomorph_smooth P04)

theorem terminalNeckFromOld_toOld (x₀ : H.regularRegion P04)
    (x : (H.extendedSliceGeometry P04 T).slice.carrier) :
    H.terminalNeckFromOld P04 ht x₀ (H.terminalNeckToOld P04 ht x) = x := by
  simp only [terminalNeckFromOld, terminalNeckToOld, regularNeckSourceMap, Function.comp_apply]
  rw [H.reference.left_inverse, SingularRegularLimit.openRetraction_coe,
    Homeomorph.symm_apply_apply]

theorem terminalNeckToOld_fromOld (x₀ : H.regularRegion P04) (y : (F.slice t).carrier)
    (hy : H.reference.inverse t ht y ∈ H.reference.regularLimitSet) :
    H.terminalNeckToOld P04 ht (H.terminalNeckFromOld P04 ht x₀ y) = y := by
  simp only [terminalNeckFromOld, terminalNeckToOld, regularNeckSourceMap, Function.comp_apply,
    Homeomorph.apply_symm_apply]
  rw [SingularRegularLimit.openRetraction_val _ _ hy, H.reference.right_inverse]

theorem terminalNeckFromOld_smoothOn (x₀ : H.regularRegion P04) {A : Set (F.slice t).carrier}
    (hA : MapsTo (H.reference.inverse t ht) A H.reference.regularLimitSet) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (H.terminalNeckFromOld P04 ht x₀) A :=
  (H.terminalSliceHomeomorph_symm_smooth P04).comp_contMDiffOn
    (SingularRegularLimit.contMDiffOn_openRetraction_comp _ x₀
      (H.reference.inverse_smooth t ht).contMDiffOn hA)

variable {ε : ℝ} (N : GeneralizedStrongNeck F t ε)
  (x₀ : H.regularRegion P04)
  (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet)

def terminalNeckCarrier : Set (H.extendedSliceGeometry P04 T).slice.carrier :=
  H.terminalNeckToOld P04 ht ⁻¹' N.carrier

theorem terminalNeckCarrier_open : IsOpen (H.terminalNeckCarrier P04 ht N) :=
  N.carrier_open.preimage (H.terminalNeckToOld_openEmbedding P04 ht).continuous

def terminalNeckCarrierHomeomorph (x₀ : H.regularRegion P04)
    (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet) :
    H.terminalNeckCarrier P04 ht N ≃ₜ N.carrier := by
  apply (H.terminalNeckToOld_openEmbedding P04 ht).isEmbedding.homeomorphOfSubsetRange
  intro y hy
  exact ⟨H.terminalNeckFromOld P04 ht x₀ y,
    H.terminalNeckToOld_fromOld P04 ht x₀ y (hcapture hy)⟩

theorem terminalNeckCarrierHomeomorph_symm_apply (y : N.carrier) :
    ((H.terminalNeckCarrierHomeomorph P04 ht N x₀ hcapture).symm y :
      (H.extendedSliceGeometry P04 T).slice.carrier) = H.terminalNeckFromOld P04 ht x₀ y := by
  apply (H.terminalNeckToOld_openEmbedding P04 ht).injective
  rw [H.terminalNeckToOld_fromOld P04 ht x₀ y (hcapture y.property)]
  exact congrArg Subtype.val ((H.terminalNeckCarrierHomeomorph P04 ht N x₀ hcapture).apply_symm_apply y)

def terminalNeckCoordinate : NeckDomain ε ≃ₜ H.terminalNeckCarrier P04 ht N :=
  N.coordinate.trans (H.terminalNeckCarrierHomeomorph P04 ht N x₀ hcapture).symm

def terminalNeckCoordinateMap : RoundCylinderSpace → (H.extendedSliceGeometry P04 T).slice.carrier :=
  H.terminalNeckFromOld P04 ht x₀ ∘ N.coordinate_map

def terminalNeckCoordinateInverse : (H.extendedSliceGeometry P04 T).slice.carrier → RoundCylinderSpace :=
  N.coordinate_inverse ∘ H.terminalNeckToOld P04 ht

theorem terminalNeckCoordinateMap_eq (z : NeckDomain ε) :
    (H.terminalNeckCoordinate P04 ht N x₀ hcapture z : (H.extendedSliceGeometry P04 T).slice.carrier) =
      H.terminalNeckCoordinateMap P04 ht N x₀ (z.1, (z.2 : ℝ)) := by
  change ((H.terminalNeckCarrierHomeomorph P04 ht N x₀ hcapture).symm (N.coordinate z) :
    (H.extendedSliceGeometry P04 T).slice.carrier) = _
  rw [H.terminalNeckCarrierHomeomorph_symm_apply P04 ht N x₀ hcapture]
  exact congrArg (H.terminalNeckFromOld P04 ht x₀) (N.coordinate_map_eq z)

include hcapture in
theorem terminalNeckCoordinateMap_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (H.terminalNeckCoordinateMap P04 ht N x₀)
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) := by
  apply (H.terminalNeckFromOld_smoothOn P04 ht x₀ hcapture).comp N.coordinate_map_smooth
  intro z hz
  change N.coordinate_map z ∈ N.carrier
  exact N.coordinate_map_eq (z.1, ⟨z.2, hz.2⟩) ▸ (N.coordinate (z.1, ⟨z.2, hz.2⟩)).property

theorem terminalNeckCoordinateInverse_mem (x : (H.extendedSliceGeometry P04 T).slice.carrier)
    (hx : x ∈ H.terminalNeckCarrier P04 ht N) :
    (H.terminalNeckCoordinateInverse P04 ht N x).2 ∈ Ioo (-ε⁻¹) ε⁻¹ :=
  N.coordinate_inverse_mem _ hx

theorem terminalNeckCoordinateInverse_left (z : NeckDomain ε) :
    H.terminalNeckCoordinateInverse P04 ht N (H.terminalNeckCoordinate P04 ht N x₀ hcapture z) =
      (z.1, (z.2 : ℝ)) := by
  change N.coordinate_inverse (H.terminalNeckToOld P04 ht
    ((H.terminalNeckCarrierHomeomorph P04 ht N x₀ hcapture).symm (N.coordinate z))) = _
  rw [H.terminalNeckCarrierHomeomorph_symm_apply P04 ht N x₀ hcapture]
  rw [H.terminalNeckToOld_fromOld P04 ht x₀ _ (hcapture (N.coordinate z).property)]
  exact N.coordinate_inverse_left z

theorem terminalNeckCoordinateInverse_right (x : (H.extendedSliceGeometry P04 T).slice.carrier)
    (hx : x ∈ H.terminalNeckCarrier P04 ht N) :
    H.terminalNeckCoordinateMap P04 ht N x₀ (H.terminalNeckCoordinateInverse P04 ht N x) = x := by
  change H.terminalNeckFromOld P04 ht x₀ (N.coordinate_map
    (N.coordinate_inverse (H.terminalNeckToOld P04 ht x))) = x
  rw [N.coordinate_inverse_right _ hx, H.terminalNeckFromOld_toOld]

theorem terminalNeckCoordinateInverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (H.terminalNeckCoordinateInverse P04 ht N)
      (H.terminalNeckCarrier P04 ht N) :=
  N.coordinate_inverse_smooth.comp (H.terminalNeckToOld_smooth P04 ht).contMDiffOn (fun _ hx => hx)

end PoincareConjecture.SingularTimeAssumptions
