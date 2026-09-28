import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Centered
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Calibration



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

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
  (N : EpsilonNeck (F.metric t)) (x₀ : H.regularRegion P04)
  (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet)

def regularStaticNeck : EpsilonNeck ((H.terminalFlow P04).metric t) :=
  N.pullbackOpen ((H.terminalFlow P04).connection t)
    ((H.reference.forward_openEmbedding t ht).comp
      (H.regularRegion P04).isOpen.isOpenEmbedding_subtypeVal)
    (H.regularNeckSourceMap_smooth P04 ht)
    (SingularRegularLimit.contMDiffOn_openRetraction_comp (H.regularRegion P04) x₀
      (H.reference.inverse_smooth t ht).contMDiffOn hcapture)
    (by
      intro x
      change SingularRegularLimit.openRetraction (H.regularRegion P04) x₀
        (H.reference.inverse t ht (H.reference.forward t ht x)) = x
      rw [H.reference.left_inverse, SingularRegularLimit.openRetraction_coe])
    (by
      intro y hy
      change H.reference.forward t ht
        (SingularRegularLimit.openRetraction (H.regularRegion P04) x₀
          (H.reference.inverse t ht y) : M) = y
      rw [SingularRegularLimit.openRetraction_val _ _ (hcapture hy), H.reference.right_inverse])
    (H.regularNeckSourceMap_metric P04 ht)

theorem regularStaticNeck_epsilon :
    (H.regularStaticNeck P04 ht N x₀ hcapture).epsilon = N.epsilon := rfl

theorem regularStaticNeck_scale :
    (H.regularStaticNeck P04 ht N x₀ hcapture).scale = N.scale := rfl

theorem regularStaticNeck_connection :
    (H.regularStaticNeck P04 ht N x₀ hcapture).connection = (H.terminalFlow P04).connection t := rfl

theorem regularStaticNeck_center_val :
    ((H.regularStaticNeck P04 ht N x₀ hcapture).center : M) = H.reference.inverse t ht N.center :=
  SingularRegularLimit.openRetraction_val _ _
    (hcapture (N.central_sphere_subset N.center_on_central_sphere))

theorem regularStaticNeck_scalar_center :
    (H.regularStaticNeck P04 ht N x₀ hcapture).connection.scalarCurvature
        (H.regularStaticNeck P04 ht N x₀ hcapture).center =
      N.connection.scalarCurvature N.center := by
  rw [H.regularStaticNeck_connection, H.terminalFlow_scalar_of_ne P04 ht.2.ne]
  change (H.reference.flow.connection t).scalarCurvature _ = _
  rw [H.regularStaticNeck_center_val,
    ← H.reference.scalar_pullback t ht (H.reference.inverse t ht N.center),
    H.reference.right_inverse]
  exact ((F.connection t).scalarCurvature_eq N.connection N.center)

theorem regularStaticNeck_carrier :
    (H.regularStaticNeck P04 ht N x₀ hcapture).carrier =
      H.regularReferencePreimage P04 t ht N.carrier := rfl

theorem regularStaticNeck_region (a b : ℝ) :
    (H.regularStaticNeck P04 ht N x₀ hcapture).region a b =
      H.regularReferencePreimage P04 t ht (N.region a b) := rfl

theorem regularStaticNeck_coordinate_map :
    (H.regularStaticNeck P04 ht N x₀ hcapture).coordinate_map =
      SingularRegularLimit.openRetraction (H.regularRegion P04) x₀ ∘
        H.reference.inverse t ht ∘ N.coordinate_map := rfl

theorem regularStaticNeck_coordinate_inverse :
    (H.regularStaticNeck P04 ht N x₀ hcapture).coordinate_inverse =
      N.coordinate_inverse ∘ H.regularNeckSourceMap P04 ht := rfl

theorem regularStaticNeck_coordinate_val (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ((H.regularStaticNeck P04 ht N x₀ hcapture).coordinate_map z : M) =
      H.reference.inverse t ht (N.coordinate_map z) :=
  SingularRegularLimit.openRetraction_val _ _ (hcapture (N.coordinate_map_mem ⟨mem_univ _, hz⟩))

end PoincareConjecture.SingularTimeAssumptions
