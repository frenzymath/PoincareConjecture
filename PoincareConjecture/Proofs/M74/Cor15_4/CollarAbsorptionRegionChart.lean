import PoincareConjecture.Proofs.M54.ConnectedSum.Coordinates
import PoincareConjecture.Proofs.M74.Mathlib.OpenTargetLift

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryRegionEquivalence

variable {A C : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set C.carrier}
  (e : SurgeryRegionEquivalence A C U V) (hU : IsOpen U)
  (E : Diffeomorph (𝓡 3) (𝓡 3) (⟨U, hU⟩ : TopologicalSpace.Opens A.carrier)
    StandardCapSpace ∞)

noncomputable def euclideanEndMap (x : C.carrier) : StandardCapSpace :=
  E ((⟨U, hU⟩ : TopologicalSpace.Opens A.carrier).liftMap (E.symm 0) e.inverse x)

noncomputable def euclideanEndInverse (z : StandardCapSpace) : C.carrier :=
  e.map (E.symm z).val

theorem euclideanEndMap_map (a : (⟨U, hU⟩ : TopologicalSpace.Opens A.carrier)) :
    e.euclideanEndMap hU E (e.map a.val) = E a := by
  unfold euclideanEndMap
  apply congrArg E
  apply Subtype.ext
  have hi : e.inverse (e.map a.val) ∈ U := by
    rw [e.left_inverse a.property]
    exact a.property
  rw [TopologicalSpace.Opens.liftMap_val_of_mem _ _ _ hi, e.left_inverse a.property]

theorem euclideanEndInverse_map {x : C.carrier} (hx : x ∈ V) :
    e.euclideanEndInverse hU E (e.euclideanEndMap hU E x) = x := by
  unfold euclideanEndInverse euclideanEndMap
  rw [E.symm_apply_apply, TopologicalSpace.Opens.liftMap_val_of_mem _ _ _
    (e.inverse_image.subset (mem_image_of_mem _ hx))]
  exact e.right_inverse hx

theorem euclideanEndMap_inverse (z : StandardCapSpace) :
    e.euclideanEndMap hU E (e.euclideanEndInverse hU E z) = z := by
  rw [euclideanEndInverse, e.euclideanEndMap_map hU E, E.apply_symm_apply]

theorem euclideanEndMap_contMDiffOn :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.euclideanEndMap hU E) V :=
  E.contMDiff.comp_contMDiffOn
    ((⟨U, hU⟩ : TopologicalSpace.Opens A.carrier).contMDiffOn_liftMap (E.symm 0)
      e.inverse_smooth (fun _ hx => e.inverse_image.subset (mem_image_of_mem _ hx)))

theorem euclideanEndInverse_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (e.euclideanEndInverse hU E) := by
  intro z
  exact (e.map_smooth.contMDiffAt (hU.mem_nhds (E.symm z).property)).comp z
    (contMDiff_subtype_val.contMDiffAt.comp z E.symm.contMDiffAt)

noncomputable def euclideanEndChart (hV : IsOpen V) :
    OpenPartialHomeomorph C.carrier StandardCapSpace where
  toFun := e.euclideanEndMap hU E
  invFun := e.euclideanEndInverse hU E
  source := V
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := e.map_image.subset (mem_image_of_mem _ (E.symm z).property)
  left_inv' _ hx := e.euclideanEndInverse_map hU E hx
  right_inv' z _ := e.euclideanEndMap_inverse hU E z
  open_source := hV
  open_target := isOpen_univ
  continuousOn_toFun := (e.euclideanEndMap_contMDiffOn hU E).continuousOn
  continuousOn_invFun := (e.euclideanEndInverse_contMDiff hU E).continuous.continuousOn

@[simp] theorem euclideanEndChart_source (hV : IsOpen V) :
    (e.euclideanEndChart hU E hV).source = V := rfl

@[simp] theorem euclideanEndChart_target (hV : IsOpen V) :
    (e.euclideanEndChart hU E hV).target = univ := rfl

theorem euclideanEndChart_map (hV : IsOpen V)
    (a : (⟨U, hU⟩ : TopologicalSpace.Opens A.carrier)) :
    e.euclideanEndChart hU E hV (e.map a.val) = E a :=
  e.euclideanEndMap_map hU E a

end PoincareConjecture.SurgeryRegionEquivalence
