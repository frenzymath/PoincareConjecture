import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.CompactCapture



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
  {t ε : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
  (N : GeneralizedStrongNeck F t ε) (x₀ : H.regularRegion P04)

def terminalNeckCentralSphere : Set (H.extendedSliceGeometry P04 T).slice.carrier :=
  H.terminalNeckFromOld P04 ht x₀ '' N.central_sphere

theorem terminalNeckCentralSphere_eq :
    H.terminalNeckCentralSphere P04 ht N x₀ =
      H.terminalNeckCoordinateMap P04 ht N x₀ '' (univ ×ˢ ({0} : Set ℝ)) := by
  rw [terminalNeckCentralSphere, N.central_sphere_eq, image_image]
  rfl

theorem terminalNeckCentralSphere_subset
    (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet) :
    H.terminalNeckCentralSphere P04 ht N x₀ ⊆ H.terminalNeckCarrier P04 ht N := by
  rintro z ⟨y, hy, rfl⟩
  have hyN := N.central_sphere_subset hy
  change H.terminalNeckToOld P04 ht (H.terminalNeckFromOld P04 ht x₀ y) ∈ N.carrier
  rw [H.terminalNeckToOld_fromOld P04 ht x₀ y (hcapture hyN)]
  exact hyN

theorem terminalNeckFromOld_center
    (hcenter : N.center = H.reference.forward t ht x₀) :
    H.terminalNeckFromOld P04 ht x₀ N.center = (H.terminalSliceHomeomorph P04).symm x₀ := by
  rw [hcenter]
  change (H.terminalSliceHomeomorph P04).symm
    (SingularRegularLimit.openRetraction (H.regularRegion P04) x₀
      (H.reference.inverse t ht (H.reference.forward t ht x₀))) = _
  rw [H.reference.left_inverse, SingularRegularLimit.openRetraction_coe]

theorem terminalNeckCenter_on_centralSphere
    (hcenter : N.center = H.reference.forward t ht x₀) :
    (H.terminalSliceHomeomorph P04).symm x₀ ∈ H.terminalNeckCentralSphere P04 ht N x₀ :=
  ⟨N.center, N.center_on_central_sphere, H.terminalNeckFromOld_center P04 ht N x₀ hcenter⟩

theorem terminalNeckCenter_mem
    (hcenter : N.center = H.reference.forward t ht x₀) :
    (H.terminalSliceHomeomorph P04).symm x₀ ∈ H.terminalNeckCarrier P04 ht N := by
  change H.reference.forward t ht ((H.terminalSliceHomeomorph P04)
    ((H.terminalSliceHomeomorph P04).symm x₀)) ∈ N.carrier
  rw [Homeomorph.apply_symm_apply, ← hcenter]
  exact N.central_sphere_subset N.center_on_central_sphere

end PoincareConjecture.SingularTimeAssumptions

namespace PoincareConjecture.SingularRegularLimit



theorem exists_late_neck_coordinate_capture_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}),
        H.epsilon ≤ ε₀ → ∀ x : H.regularRegion P04,
          ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
            ∀ t (ht : t ∈ Ico H.reference.tMinus T), s ≤ t →
              ∀ N : GeneralizedStrongNeck F t H.epsilon,
                N.center = H.reference.forward t ht x →
                  MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet := by
  obtain ⟨ε₀, hε₀, hsmall, hcapture⟩ := exists_neck_cap_compact_capture_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H P04 hε x
  obtain ⟨A, _, hA, s, hs, hsT, hlate⟩ := hcapture H P04 hε x x.property
  refine ⟨s, hs, hsT, ?_⟩
  intro t ht hst N hc y hy
  exact hA ((hlate t ht hst).1 N hc (subset_closure (mem_image_of_mem _ hy)))

end PoincareConjecture.SingularRegularLimit
