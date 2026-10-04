import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry
import PoincareLib.Geometry.Manifold.InverseFunction

/-!
# Open spatial maps of the actual blowup cylinders

Morgan--Tian Claim 11.34, printed pp. 288-289, uses the spatial embeddings
of the generalized-flow limit. The stored smooth inverse first makes the
spatial derivative injective; equal dimension and the inverse function
theorem then give openness of the image.

Re-derived from read-only `GeneralizedFlowCylinder.horizon_forward_mfderiv_bijective`
and `horizon_isOpen_forward_image` in DeepHorn `Limit/NeckTransfer.lean`.
No Surgery or M34 proof module is imported. The reviewed derivation is
`proof-work/tasks/M32/derivations/claim11_34-first-stage.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M32

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}

/-- The stored inverse gives a bijective spatial derivative on an open
cylinder source, as used in Claim 11.34, printed pp. 288-289. -/
theorem cylinder_forward_mfderiv_bijective
    (d : GeneralizedFlowCylinder F C a q J U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ J) {x : C.carrier} (hx : x ∈ U) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x) := by
  have hf := (d.forward_smooth s hs x hx).mdifferentiableWithinAt (by simp)
  have hi := (d.inverse_smooth s hs (d.forward s hs x)
    (mem_image_of_mem (d.forward s hs) hx)).mdifferentiableWithinAt (by simp)
  have hc := mfderivWithin_comp x hi hf
    (fun y hy => mem_image_of_mem (d.forward s hs) hy) (hU.uniqueMDiffOn x hx)
  have hid : mfderivWithin (𝓡 3) (𝓡 3)
      (d.inverse s hs ∘ d.forward s hs) U x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
    have heq := mfderivWithin_congr_of_mem (I := 𝓡 3) (I' := 𝓡 3)
      (f := id) (f₁ := d.inverse s hs ∘ d.forward s hs)
      (fun y hy => d.left_inverse s hs hy) hx
    exact heq.trans (mfderivWithin_id (hU.uniqueMDiffOn x hx))
  rw [hid, mfderivWithin_eq_mfderiv (hU.uniqueMDiffOn x hx)
    (hf.mdifferentiableAt (hU.mem_nhds hx))] at hc
  have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x) := by
    intro v w hvw
    have hv := congrArg (fun A => A v) hc
    have hw := congrArg (fun A => A w) hc
    change v = mfderivWithin (𝓡 3) (𝓡 3) (d.inverse s hs)
      (d.forward s hs '' U) (d.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x v) at hv
    change w = mfderivWithin (𝓡 3) (𝓡 3) (d.inverse s hs)
      (d.forward s hs '' U) (d.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x w) at hw
    rw [hvw] at hv
    exact hv.trans hw.symm
  dsimp only [TangentSpace] at hinj ⊢
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- An open cylinder source has open spatial image in its actual target
slice, as needed in Claim 11.34, printed pp. 288-289. -/
theorem cylinder_isOpen_forward_image
    (d : GeneralizedFlowCylinder F C a q J U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ J) : IsOpen (d.forward s hs '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx))
    (cylinder_forward_mfderiv_bijective d hU s hs hx)]
  change (d.forward s hs) ⁻¹' (d.forward s hs '' U) ∈ 𝓝 x
  exact mem_of_superset (hU.mem_nhds hx) (fun z hz => mem_image_of_mem _ hz)

end PoincareMT.M32
