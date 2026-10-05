import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Coordinates
import PoincareLib.Topology.Manifold.Surgery.Reduction.Algebra.OpenTargetLift

/-!
# Transport of an actual exterior coordinate to its connected-sum region

The smooth region equivalence and the Euclidean exterior diffeomorphism
give a genuine chart with the exact open region as source. This is the
cap-coordinate transport in MT Corollary 15.4(2), pp. 358-359.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.SurgeryRegionEquivalence

variable {A C : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set C.carrier}
  (e : SurgeryRegionEquivalence A C U V) (hU : IsOpen U)
  (E : Diffeomorph (𝓡 3) (𝓡 3) (⟨U, hU⟩ : TopologicalSpace.Opens A.carrier)
    StandardCapSpace ∞)

/-- The controlled lift totalizes the Euclidean coordinate without
changing its values on the region (MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def euclideanEndMap (x : C.carrier) : StandardCapSpace :=
  E ((⟨U, hU⟩ : TopologicalSpace.Opens A.carrier).liftMap (E.symm 0) e.inverse x)

/-- The Euclidean inverse has values in the actual connected-sum region
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def euclideanEndInverse (z : StandardCapSpace) : C.carrier :=
  e.map (E.symm z).val

/-- Transport preserves the exact exterior-coordinate value
(MT Corollary 15.4(2), pp. 358-359). -/
theorem euclideanEndMap_map (a : (⟨U, hU⟩ : TopologicalSpace.Opens A.carrier)) :
    e.euclideanEndMap hU E (e.map a.val) = E a := by
  unfold euclideanEndMap
  apply congrArg E
  apply Subtype.ext
  have hi : e.inverse (e.map a.val) ∈ U := by
    rw [e.left_inverse a.property]
    exact a.property
  rw [TopologicalSpace.Opens.liftMap_val_of_mem _ _ _ hi, e.left_inverse a.property]

/-- The transported inverse recovers every region point
(MT Corollary 15.4(2), pp. 358-359). -/
theorem euclideanEndInverse_map {x : C.carrier} (hx : x ∈ V) :
    e.euclideanEndInverse hU E (e.euclideanEndMap hU E x) = x := by
  unfold euclideanEndInverse euclideanEndMap
  rw [E.symm_apply_apply, TopologicalSpace.Opens.liftMap_val_of_mem _ _ _
    (e.inverse_image.subset (mem_image_of_mem _ hx))]
  exact e.right_inverse hx

/-- The transported coordinate recovers every Euclidean point
(MT Corollary 15.4(2), pp. 358-359). -/
theorem euclideanEndMap_inverse (z : StandardCapSpace) :
    e.euclideanEndMap hU E (e.euclideanEndInverse hU E z) = z := by
  rw [euclideanEndInverse, e.euclideanEndMap_map hU E, E.apply_symm_apply]

/-- The transported coordinate is smooth on precisely its controlled
region (MT Corollary 15.4(2), pp. 358-359). -/
theorem euclideanEndMap_contMDiffOn :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.euclideanEndMap hU E) V :=
  E.contMDiff.comp_contMDiffOn
    ((⟨U, hU⟩ : TopologicalSpace.Opens A.carrier).contMDiffOn_liftMap (E.symm 0)
      e.inverse_smooth (fun _ hx => e.inverse_image.subset (mem_image_of_mem _ hx)))

/-- The inverse coordinate is smooth on all Euclidean space
(MT Corollary 15.4(2), pp. 358-359). -/
theorem euclideanEndInverse_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (e.euclideanEndInverse hU E) := by
  intro z
  exact (e.map_smooth.contMDiffAt (hU.mem_nhds (E.symm z).property)).comp z
    (contMDiff_subtype_val.contMDiffAt.comp z E.symm.contMDiffAt)

/-- The exact cap chart transported through the supplied smooth region
equivalence (MT Corollary 15.4(2), pp. 358-359). -/
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

/-- The cap chart has exactly the displayed region as source
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem euclideanEndChart_source (hV : IsOpen V) :
    (e.euclideanEndChart hU E hV).source = V := rfl

/-- Its target is all Euclidean space
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem euclideanEndChart_target (hV : IsOpen V) :
    (e.euclideanEndChart hU E hV).target = univ := rfl

/-- The chart retains the exact exterior formula on every source point
(MT Corollary 15.4(2), pp. 358-359). -/
theorem euclideanEndChart_map (hV : IsOpen V)
    (a : (⟨U, hU⟩ : TopologicalSpace.Opens A.carrier)) :
    e.euclideanEndChart hU E hV (e.map a.val) = E a :=
  e.euclideanEndMap_map hU E a

end PoincareMT.SurgeryRegionEquivalence
