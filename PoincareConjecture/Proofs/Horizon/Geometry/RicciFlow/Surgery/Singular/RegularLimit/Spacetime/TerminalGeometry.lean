import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.SliceIdentifications
import Mathlib.Topology.Connected.LocallyPathConnected

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularRegularLimit.SliceGeometry

theorem compactSingularMetricLimit_of_eq
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (R : SingularTimeReference F T M) {G K : SliceGeometry.{u}}
    (h : G = K) (i : K.slice.carrier → M)
    (hlimit : CompactSingularMetricLimit R K.metric i) :
    CompactSingularMetricLimit R G.metric (i ∘ homeomorphOfEq h) := by
  subst K
  exact hlimit

end PoincareConjecture.SingularRegularLimit.SliceGeometry

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

def terminalSource (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    (H.extendedSliceGeometry P04 T).slice.carrier → M :=
  Subtype.val ∘ H.terminalSliceHomeomorph P04

theorem terminalSource_image (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    range (H.terminalSource P04) = H.reference.regularLimitSet := by
  rw [terminalSource, range_comp, (H.terminalSliceHomeomorph P04).surjective.range_eq,
    image_univ]
  exact Subtype.range_val

theorem terminalSource_openEmbedding (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    Topology.IsOpenEmbedding (H.terminalSource P04) :=
  (H.regularRegion P04).isOpen.isOpenEmbedding_subtypeVal.comp
    (H.terminalSliceHomeomorph P04).isOpenEmbedding

theorem terminalSource_smooth (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (H.terminalSource P04) :=
  contMDiff_subtype_val.comp (H.terminalSliceHomeomorph_smooth P04)

theorem terminalSource_regular (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u})
    (x : (H.extendedSliceGeometry P04 T).slice.carrier) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (H.terminalSource P04) x) := by
  rw [terminalSource, mfderiv_comp x
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) _)
    ((H.terminalSliceHomeomorph_smooth P04).mdifferentiable (by simp) x),
    Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
  exact H.terminalSliceHomeomorph_mfderiv_bijective P04 x

theorem compactSingularMetricLimit_extended_terminal
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    CompactSingularMetricLimit H.reference (H.extendedSliceGeometry P04 T).metric
      (H.terminalSource P04) :=
  SingularRegularLimit.SliceGeometry.compactSingularMetricLimit_of_eq H.reference
    (G := H.extendedSliceGeometry P04 T) (K := H.terminalSliceGeometry P04)
    (H.extendedSliceGeometry_terminal P04) Subtype.val
    (H.compactSingularMetricLimit_terminalMetric P04)

theorem extended_terminal_scalar_proper_and_bounded_below
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    (∃ L : ℝ, ∀ x, L ≤ (H.extendedSliceGeometry P04 T).connection.scalarCurvature x) ∧
      ∀ K : Set ℝ, IsCompact K →
        IsCompact ((H.extendedSliceGeometry P04 T).connection.scalarCurvature ⁻¹' K) := by
  obtain ⟨⟨L, hL⟩, hproper⟩ := H.terminal_scalarCurvature_proper_and_bounded_below P04
  constructor
  · refine ⟨L, fun x => ?_⟩
    rw [← H.terminalSliceHomeomorph_scalar_pullback P04 x]
    exact hL _
  · intro K hK
    have heq : (H.extendedSliceGeometry P04 T).connection.scalarCurvature ⁻¹' K =
        (H.terminalSliceHomeomorph P04) ⁻¹'
          ((H.terminalConnection P04).scalarCurvature ⁻¹' K) := by
      ext x
      simp only [mem_preimage, H.terminalSliceHomeomorph_scalar_pullback P04 x]
    rw [heq]
    exact (H.terminalSliceHomeomorph P04).isCompact_preimage.mpr (hproper K hK)

end PoincareConjecture.SingularTimeAssumptions

namespace PoincareConjecture.SingularRegularLimit

def terminalComponentPath {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (E : GeneralizedFlowExtension F T) (x : (E.extended.slice T).carrier) :
    TerminalComponentPath E where
  basepoint := x
  component := connectedComponent x
  component_eq := rfl
  path_to y hy := by
    let _ : LocallyPathConnectedSpace (E.extended.slice T).carrier :=
      ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
    have hp : IsPathConnected (connectedComponent x) := by
      rw [← pathComponent_eq_connectedComponent]
      exact isPathConnected_pathComponent
    obtain ⟨γ, hγ⟩ := hp.joinedIn x mem_connectedComponent y hy
    exact ⟨γ, fun z ⟨s, hs⟩ => hs ▸ hγ s⟩

end PoincareConjecture.SingularRegularLimit
