import PoincareConjecture.Proofs.M12.GeneralizedCylinderClock
import PoincareConjecture.Proofs.M11.OpenSubsetDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

open PoincareConjecture.Proofs.M11

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)

theorem rawForward_differential_injective (s : J.domain) (x : U) :
    Injective (mfderiv (𝓡 3) (𝓡 3) (e.forward s.val s.property) x.val) := by
  have hf := (e.forward_smooth s.val s.property x.val x.property).mdifferentiableWithinAt
    (by simp)
  have hg := (e.inverse_smooth s.val s.property (e.forward s.val s.property x.val)
    (mem_image_of_mem _ x.property)).mdifferentiableWithinAt (by simp)
  have hunique := U.isOpen.uniqueMDiffWithinAt (I := 𝓡 3) x.property
  have hcomp := mfderivWithin_comp x.val hg hf
    (fun y hy => mem_image_of_mem (e.forward s.val s.property) hy) hunique
  have hid : mfderivWithin (𝓡 3) (𝓡 3)
      (e.inverse s.val s.property ∘ e.forward s.val s.property) U x.val =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) x.val) :=
    (mfderivWithin_congr_of_mem (e.left_inverse s.val s.property) x.property).trans
      (mfderivWithin_id hunique)
  rw [hid, mfderivWithin_eq_mfderiv hunique
    (hf.mdifferentiableAt (U.isOpen.mem_nhds x.property))] at hcomp
  intro v w hvw
  have hv := congrArg (fun l : TangentSpace (𝓡 3) x.val →L[ℝ]
    TangentSpace (𝓡 3) x.val => l v) hcomp
  have hw := congrArg (fun l : TangentSpace (𝓡 3) x.val →L[ℝ]
    TangentSpace (𝓡 3) x.val => l w) hcomp
  exact hv.trans ((congrArg (mfderivWithin (𝓡 3) (𝓡 3) (e.inverse s.val s.property)
    (e.forward s.val s.property '' U) (e.forward s.val s.property x.val)) hvw).trans hw.symm)

def rawSpatialMap (s : J.domain) : U → (F.slice (a + s.val / q)).carrier :=
  fun x => e.forward s.val s.property x.val

theorem rawSpatialMap_smooth (s : J.domain) : ContMDiff (𝓡 3) (𝓡 3) ∞ (rawSpatialMap e s) :=
  (e.forward_smooth s.val s.property).comp_contMDiff contMDiff_subtype_val
    (fun x => x.property)

theorem rawSpatialMap_differential_injective (s : J.domain) (x : U) :
    Injective (mfderiv (𝓡 3) (𝓡 3) (rawSpatialMap e s) x) := by
  have hf := (e.forward_smooth s.val s.property x.val x.property).contMDiffAt
    (U.isOpen.mem_nhds x.property)
  change Injective (mfderiv (𝓡 3) (𝓡 3)
    (e.forward s.val s.property ∘ (Subtype.val : U → C.carrier)) x)
  rw [mfderiv_comp x (hf.mdifferentiableAt (by simp))
    (contMDiff_subtype_val (n := ∞) x |>.mdifferentiableAt (by simp))]
  exact (rawForward_differential_injective e s x).comp
    (openSubset_differential_injective U x)

end PoincareConjecture.Proofs.M12
