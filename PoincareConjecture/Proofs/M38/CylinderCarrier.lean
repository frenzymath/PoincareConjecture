import PoincareConjecture.Proofs.M38.ProjectivePolarCover
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Covering.LocalDiffeomorph











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38


noncomputable def cylinderAtlasProjection (x : ULift.{u} RoundCylinderSpace) :
    projectiveCarrier.{u}.carrier :=
  projectivePolarMap (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4))) x.down


theorem cylinderAtlasProjection_localHomeomorph :
    IsLocalHomeomorph cylinderAtlasProjection.{u} :=
  (projectivePolar_localDiffeomorph
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4)))).isLocalHomeomorph.comp
      (Homeomorph.ulift : ULift.{u} RoundCylinderSpace ≃ₜ RoundCylinderSpace).isLocalHomeomorph


@[instance_reducible]
noncomputable def cylinderLiftChartedSpace :
    ChartedSpace StandardCapSpace (ULift.{u} RoundCylinderSpace) :=
  Poincare.Manifold.LocalHomeomorphLift.chartedSpace
    (H := StandardCapSpace) cylinderAtlasProjection_localHomeomorph

attribute [local instance] cylinderLiftChartedSpace


noncomputable def cylinderCarrier : GeneralizedSliceCarrier.{u} := by
  let h := cylinderAtlasProjection_localHomeomorph.{u}
  let := Poincare.Manifold.LocalHomeomorphLift.isManifold h (𝓡 3) ∞
  let : MeasurableSpace (ULift.{u} RoundCylinderSpace) := borel _
  let : BorelSpace (ULift.{u} RoundCylinderSpace) := ⟨rfl⟩
  exact {
    carrier := ULift.{u} RoundCylinderSpace
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := inferInstance
    chartedSpace := inferInstance
    isManifold := inferInstance
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := Homeomorph.ulift.secondCountableTopology }


theorem cylinderCarrier_projection_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (cylinderAtlasProjection : cylinderCarrier.{u}.carrier → projectiveCarrier.carrier) :=
  Poincare.Manifold.LocalHomeomorphLift.isLocalDiffeomorph
    cylinderAtlasProjection_localHomeomorph (𝓡 3) ∞


theorem cylinderCarrier_up_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (ULift.up : RoundCylinderSpace → cylinderCarrier.{u}.carrier) := by
  intro p
  let h := cylinderCarrier_projection_localDiffeomorph (ULift.up p)
  have hp := (projectivePolar_localDiffeomorph
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4)))).contMDiff p
  have hs := h.localInverse_contMDiffAt.comp p hp
  apply hs.congr_of_eventuallyEq
  filter_upwards [continuous_uliftUp.continuousAt.preimage_mem_nhds
    (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)] with x hx
  exact (h.localInverse_left_inv hx).symm


theorem cylinderCarrier_down_smooth : ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
    (ULift.down : cylinderCarrier.{u}.carrier → RoundCylinderSpace) := by
  intro p
  let h := projectivePolar_localDiffeomorph
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4))) p.down
  have hs := h.localInverse_contMDiffAt.comp p
    (cylinderCarrier_projection_localDiffeomorph.contMDiff p)
  apply hs.congr_of_eventuallyEq
  filter_upwards [continuous_uliftDown.continuousAt.preimage_mem_nhds
    (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)] with x hx
  exact (h.localInverse_left_inv hx).symm


noncomputable def cylinderCarrierDiffeomorph :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace cylinderCarrier.{u}.carrier ∞ where
  toEquiv := Equiv.ulift.symm
  contMDiff_toFun := cylinderCarrier_up_smooth
  contMDiff_invFun := cylinderCarrier_down_smooth

end PoincareConjecture.M38
