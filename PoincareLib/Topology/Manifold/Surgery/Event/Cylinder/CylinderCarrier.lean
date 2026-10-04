import PoincareLib.Topology.Manifold.Surgery.Event.Projective.ProjectivePolarCover
import PoincareLib.Geometry.Manifold.Covering.LocalDiffeomorph

/-!
# The literal smooth cylinder as a three-dimensional carrier

The underlying space is the universe lift of the original round cylinder.
Its three-dimensional atlas is lifted through the actual polar projection;
the identity of the underlying cylinder is a diffeomorphism from the
original product atlas. No cylindrical model is postulated.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- The literal lifted cylinder projects through the fixed polar coordinates. -/
noncomputable def cylinderAtlasProjection (x : ULift.{u} RoundCylinderSpace) :
    projectiveCarrier.{u}.carrier :=
  projectivePolarMap (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4))) x.down

/-- The unchanged projection is locally a homeomorphism before choosing any lifted atlas. -/
theorem cylinderAtlasProjection_localHomeomorph :
    IsLocalHomeomorph cylinderAtlasProjection.{u} :=
  (projectivePolar_localDiffeomorph
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4)))).isLocalHomeomorph.comp
      (Homeomorph.ulift : ULift.{u} RoundCylinderSpace ≃ₜ RoundCylinderSpace).isLocalHomeomorph

/-- The lifted atlas uses the original product topology and polar projection. -/
@[instance_reducible]
noncomputable def cylinderLiftChartedSpace :
    ChartedSpace StandardCapSpace (ULift.{u} RoundCylinderSpace) :=
  Poincare.Manifold.LocalHomeomorphLift.chartedSpace
    (H := StandardCapSpace) cylinderAtlasProjection_localHomeomorph

attribute [local instance] cylinderLiftChartedSpace

/-- The actual cylinder with its lifted three-dimensional smooth atlas. -/
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

/-- The literal projection is smooth and locally invertible for this same atlas. -/
theorem cylinderCarrier_projection_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (cylinderAtlasProjection : cylinderCarrier.{u}.carrier → projectiveCarrier.carrier) :=
  Poincare.Manifold.LocalHomeomorphLift.isLocalDiffeomorph
    cylinderAtlasProjection_localHomeomorph (𝓡 3) ∞

/-- Universe lifting of the original cylinder is smooth into the constructed carrier. -/
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

/-- Projection to the original product cylinder is smooth in the reverse direction. -/
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

/-- The actual cylinder diffeomorphism keeps every point, angle and real coordinate. -/
noncomputable def cylinderCarrierDiffeomorph :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace cylinderCarrier.{u}.carrier ∞ where
  toEquiv := Equiv.ulift.symm
  contMDiff_toFun := cylinderCarrier_up_smooth
  contMDiff_invFun := cylinderCarrier_down_smooth

end PoincareMT.M38
