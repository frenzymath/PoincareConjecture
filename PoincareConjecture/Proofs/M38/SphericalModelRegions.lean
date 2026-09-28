import PoincareConjecture.Proofs.M38.SpherePunctureCoordinates
import PoincareConjecture.Proofs.M38.CylinderRegionTransport
import PoincareConjecture.Proofs.M38.RoundExteriorCylinder
import PoincareConjecture.Proofs.M38.FullCutLocalModels










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

variable {A : GeneralizedSliceCarrier.{u}} {U : Set A.carrier}



noncomputable def closedSphereRegionEquivalence
    (C : SmoothClosedComponentModel .threeSphere U) :
    SurgeryRegionEquivalence A sphereCarrier.{u} U univ := by
  letI := C.model_topology
  letI := C.model_charted
  letI := C.model_manifold
  let d := C.standard_smooth.some
  exact {
    map := fun x => ULift.up (d (C.inverse x))
    inverse := fun y => C.forward (d.symm y.down)
    map_image := by
      apply subset_antisymm (subset_univ _)
      intro y _
      exact ⟨C.forward (d.symm y.down), C.forward_mem _, by
        simp only [C.right_inverse, d.apply_symm_apply]
        rfl⟩
    inverse_image := by
      apply subset_antisymm
      · rintro _ ⟨y, _, rfl⟩
        exact C.forward_mem _
      · intro x hx
        exact ⟨ULift.up (d (C.inverse x)), mem_univ _, by
          simp only [d.symm_apply_apply, C.left_inverse x hx]⟩
    left_inverse := by
      intro x hx
      simp only [d.symm_apply_apply, C.left_inverse x hx]
    right_inverse := by
      intro y _
      simp only [C.right_inverse, d.apply_symm_apply]
      rfl
    map_smooth := (threeManifold_up_contMDiff UnitThreeSphere).comp_contMDiffOn
      (d.contMDiff.comp_contMDiffOn C.inverse_smooth)
    inverse_smooth := (C.forward_smooth.comp
      (d.symm.contMDiff.comp (threeManifold_down_contMDiff UnitThreeSphere))).contMDiffOn }



noncomputable def euclideanCapRegionEquivalence {p : RealProjectiveThree}
    (C : CapModelEquivalence .euclidean p U) :
    SurgeryRegionEquivalence A euclideanCarrier.{u} U univ := by
  letI := C.model_topology
  letI := C.model_charted
  letI := C.model_manifold
  let d := C.standard_smooth.some
  exact {
    map := fun x => ULift.up (d (C.forward x))
    inverse := fun y => C.inverse (d.symm y.down)
    map_image := by
      apply subset_antisymm (subset_univ _)
      intro y _
      exact ⟨C.inverse (d.symm y.down), C.inverse_mem _, by
        simp only [C.right_inverse, d.apply_symm_apply]
        rfl⟩
    inverse_image := by
      apply subset_antisymm
      · rintro _ ⟨y, _, rfl⟩
        exact C.inverse_mem _
      · intro x hx
        exact ⟨ULift.up (d (C.forward x)), mem_univ _, by
          simp only [d.symm_apply_apply, C.left_inverse x hx]⟩
    left_inverse := by
      intro x hx
      simp only [d.symm_apply_apply, C.left_inverse x hx]
    right_inverse := by
      intro y _
      simp only [C.right_inverse, d.apply_symm_apply]
      rfl
    map_smooth := (threeManifold_up_contMDiff StandardCapSpace).comp_contMDiffOn
      (d.contMDiff.comp_contMDiffOn C.forward_smooth)
    inverse_smooth := (contMDiffOn_univ.mp C.inverse_smooth).comp_contMDiffOn
      (d.symm.contMDiff.comp (threeManifold_down_contMDiff StandardCapSpace)).contMDiffOn }



noncomputable def cylinderExteriorEquivalence (C : OpenCylinderModel U) :
    SurgeryRegionEquivalence A euclideanCarrier.{u} U {y | 1 < ‖y.down‖} := by
  let D := roundExteriorCylinder (show (0 : ℝ) < 1 from zero_lt_one)
  exact {
    map := fun x => ULift.up (D.coordinate (C.inverse x))
    inverse := fun y => C.coordinate (D.inverse y.down)
    map_image := by
      apply subset_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact roundExteriorCoordinate_mem zero_lt_one (C.inverse_mem x hx)
      · intro y hy
        refine ⟨C.coordinate (D.inverse y.down), ?_, ?_⟩
        · exact cylinderCoordinate_mem C (D.inverse_mem y.down hy)
        · simp only [C.left_inverse (D.inverse_mem y.down hy), D.right_inverse hy]
          rfl
    inverse_image := by
      apply subset_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact cylinderCoordinate_mem C (D.inverse_mem y.down hy)
      · intro x hx
        refine ⟨ULift.up (D.coordinate (C.inverse x)), ?_, ?_⟩
        · exact roundExteriorCoordinate_mem zero_lt_one (C.inverse_mem x hx)
        · simp only [D.left_inverse (C.inverse_mem x hx), C.right_inverse hx]
    left_inverse := by
      intro x hx
      simp only [D.left_inverse (C.inverse_mem x hx), C.right_inverse hx]
    right_inverse := by
      intro y hy
      simp only [C.left_inverse (D.inverse_mem y.down hy), D.right_inverse hy]
      rfl
    map_smooth := (threeManifold_up_contMDiff StandardCapSpace).comp_contMDiffOn
      (D.coordinate_smooth.comp C.inverse_smooth C.inverse_mem)
    inverse_smooth := C.coordinate_smooth.comp
      (D.inverse_smooth.comp (threeManifold_down_contMDiff StandardCapSpace).contMDiffOn
        (fun _ hy => hy)) (fun y hy => D.inverse_mem y.down hy) }



theorem exists_spherical_chart_of_euclidean_region {V : Set euclideanCarrier.{u}.carrier}
    (E : SurgeryRegionEquivalence A euclideanCarrier.{u} U V)
    (hU : IsOpen U) (hV : IsOpen V) :
    ∃ e : OpenPartialHomeomorph A.carrier sphereCarrier.{u}.carrier,
      e.source = U ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
  let p : sphereCarrier.{u}.carrier := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  let d := regionPartialDiffeomorph E hU hV
  let s := regionPartialDiffeomorph (spherePunctureEquivalence p)
    isClosed_singleton.isOpen_compl isOpen_univ
  let e := d.trans s.symm
  refine ⟨e.toOpenPartialHomeomorph, ?_, e.contMDiffOn_toFun, e.contMDiffOn_invFun⟩
  change U ∩ E.map ⁻¹' univ = U
  simp

end PoincareConjecture.M38
