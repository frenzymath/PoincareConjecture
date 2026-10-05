import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.CylinderImmersion
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.CylinderMetricRigidity
import PoincareLib.Geometry.Manifold.InverseFunction

/-!
# The actual spatial coordinates of a selected limit cylinder

Morgan-Tian Theorem 12.28, pp. 323-324. The supplied cylinder inverse
and its within-domain differential give an actual partial diffeomorphism
into the original R3. Compatibility retains one fixed spatial coordinate
throughout the normalized time interval and identifies its metric pullback.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- Theorem 12.28: the spatial map of an actual compatible cylinder
on an open source is a partial diffeomorphism into the original R3. -/
noncomputable def cylinderSpatialCoordinates {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ I) (htime : a + s / Q ∈ J) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier StandardCapSpace ∞ := by
  let d := sliceDiffeomorph htime
  let f : C.carrier → StandardCapSpace := d ∘ e.forward s hs
  let g : StandardCapSpace → C.carrier := e.inverse s hs ∘ d.symm
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
    d.contMDiff.comp_contMDiffOn (e.forward_smooth s hs)
  have hgf (x : C.carrier) (hx : x ∈ U) : g (f x) = x :=
    (congrArg (e.inverse s hs) (d.symm_apply_apply (e.forward s hs x))).trans
      (e.left_inverse s hs hx)
  refine {
    toFun := f
    invFun := g
    source := U
    target := f '' U
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := ?_
    left_inv' := hgf
    right_inv' := ?_
    open_source := hU
    open_target := ?_
    contMDiffOn_toFun := hf
    contMDiffOn_invFun := ?_
  }
  · rintro y ⟨x, hx, rfl⟩
    exact (hgf x hx).symm ▸ hx
  · rintro y ⟨x, hx, rfl⟩
    exact congrArg f (hgf x hx)
  · apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨x, hx, rfl⟩
    have hreg := (e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)
    have hderiv : Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x) := by
      rw [mfderiv_comp x (d.contMDiff.mdifferentiable (by simp) _)
        (hreg.mdifferentiableAt (by simp))]
      exact (d.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
        (e.mfderiv_injective hU s hs hx)
    let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (mfderiv (𝓡 3) (𝓡 3) f x).toLinearMap
    have hsurj : Function.Surjective L :=
      (LinearMap.injective_iff_surjective (f := L)).mp hderiv
    rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
      (hf.contMDiffAt (hU.mem_nhds hx)) ⟨hderiv, hsurj⟩]
    exact image_mem_map (hU.mem_nhds hx)
  · apply (e.inverse_smooth s hs).comp d.symm.contMDiff.contMDiffOn
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, (d.symm_apply_apply (e.forward s hs x)).symm⟩

/-- Theorem 12.28: a compatible cylinder from any actual source
pulls back the original evolving metric by its one fixed spatial map. -/
theorem cylinder_pullbackInner_eq_fixed {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hI : IsPreconnected I) (hU : IsOpen U) {s r : ℝ} (hs : s ∈ I) (hr : r ∈ I)
    {x : C.carrier} (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner s hs x v w =
      Q * (F.metric (a + s / Q)).inner (e.forward r hr x).val
        (mfderiv (𝓡 3) (𝓡 3) (fun y => (e.forward r hr y).val) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y => (e.forward r hr y).val) x w) := by
  let d := sliceDiffeomorph (e.forward s hs x).property
  have heq : EqOn (d ∘ e.forward s hs) (fun y => (e.forward r hr y).val) U :=
    fun _ hy => cylinder_spatial_eq F e hI hy hs hr
  have hevent := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heq
  have hderiv : mfderiv (𝓡 3) (𝓡 3) (d ∘ e.forward s hs) x =
      mfderiv (𝓡 3) (𝓡 3) (fun y => (e.forward r hr y).val) x := hevent.mfderiv_eq
  have hreg := (e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)
  have hd (v : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) d (e.forward s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) =
        mfderiv (𝓡 3) (𝓡 3) (fun y => (e.forward r hr y).val) x v :=
    (mfderiv_comp_apply x (d.contMDiff.mdifferentiable (by simp) _)
      (hreg.mdifferentiableAt (by simp)) v).symm.trans
        (congrArg (fun L => L v) hderiv)
  change Q * (F.metric (a + s / Q)).inner (d (e.forward s hs x))
    (mfderiv (𝓡 3) (𝓡 3) d (e.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v))
    (mfderiv (𝓡 3) (𝓡 3) d (e.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x w)) = _
  rw [hd v, hd w]
  exact congrArg (fun y : StandardCapSpace => Q * (F.metric (a + s / Q)).inner y
    (mfderiv (𝓡 3) (𝓡 3) (fun z => (e.forward r hr z).val) x v)
    (mfderiv (𝓡 3) (𝓡 3) (fun z => (e.forward r hr z).val) x w)) (heq hx)

end PoincareMT.M35.OrdinaryRealization
