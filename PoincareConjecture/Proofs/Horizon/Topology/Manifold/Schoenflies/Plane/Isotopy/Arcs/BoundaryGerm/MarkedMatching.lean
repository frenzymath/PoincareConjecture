import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Compression.Coordinates
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem exists_hemisphere_alignment
    (v w : E2) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (Jv : E1 ≃ₗᵢ[Real] Hemisphere.Plane v)
    (Jw : E1 ≃ₗᵢ[Real] Hemisphere.Plane w) :
    ∃ H : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      H '' closedBall 0 1 = closedBall 0 1 ∧
      ∀ x : E1, H (Hemisphere.toSphere hv (Jv x)) =
        (Hemisphere.toSphere hw (Jw x) : E2) := by
  let R : E2 ≃ₗᵢ[Real] E2 := (Real ∙ (v - w))ᗮ.reflection
  have hRv : R v = w := Submodule.reflection_sub (hv.trans hw.symm)
  have hRiw : R.symm w = v := by rw [← hRv, R.symm_apply_apply]
  have hRp (x : Hemisphere.Plane v) : R (x : E2) ∈ Hemisphere.Plane w := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [← hRv, R.inner_map_map]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  have hRip (x : Hemisphere.Plane w) : R.symm (x : E2) ∈ Hemisphere.Plane v := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [← hRiw, R.symm.inner_map_map]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  let Rp : Hemisphere.Plane v ≃ₗᵢ[Real] Hemisphere.Plane w := {
    toFun := fun x => ⟨R x, hRp x⟩
    invFun := fun x => ⟨R.symm x, hRip x⟩
    left_inv := fun x => Subtype.ext (R.symm_apply_apply x)
    right_inv := fun x => Subtype.ext (R.apply_symm_apply x)
    map_add' := fun x y => Subtype.ext (R.map_add x y)
    map_smul' := fun a x => Subtype.ext (R.map_smul a x)
    norm_map' := fun x => R.norm_map x }
  let T := (Rp.symm.trans Jv.symm).trans Jw
  let L := Hemisphere.extendLinear w T.toContinuousLinearEquiv
  let N := LinearBall.neighborhood L
  let P : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ := {
    toPartialEquiv := N.toPartialEquiv
    open_source := N.open_source
    open_target := N.open_target
    contMDiffOn_toFun := LinearBall.contMDiffOn_neighborhood L
    contMDiffOn_invFun := LinearBall.contMDiffOn_neighborhood_symm L }
  have hNs : closedBall (0 : E2) 1 ⊆ N.source := LinearBall.closedBall_subset_source L
  obtain ⟨F, hF⟩ := exists_global_extension_of_local_ball_embedding zero_lt_one N
    (N.injOn.mono hNs) (fun x hx => ⟨P, hNs hx, fun _ _ => rfl⟩)
  have hFball : F '' closedBall 0 1 = closedBall 0 1 := by
    calc
      F '' closedBall 0 1 = N '' closedBall 0 1 := image_congr (fun x hx => hF x hx)
      _ = closedBall 0 1 := LinearBall.image_closedBall L
  have hRchart (z : Hemisphere.Plane v) :
      R (Hemisphere.toSphere hv z : E2) = (Hemisphere.toSphere hw (Rp z) : E2) := by
    have he : ((Rp z : Hemisphere.Plane w) : E2) + w = R ((z : E2) + v) := by
      rw [R.map_add, hRv]
      rfl
    change R (‖(z : E2) + v‖⁻¹ • ((z : E2) + v)) =
      ‖((Rp z : Hemisphere.Plane w) : E2) + w‖⁻¹ •
        (((Rp z : Hemisphere.Plane w) : E2) + w)
    rw [he, R.norm_map, R.map_smul]
  let H := R.toContinuousLinearEquiv.toDiffeomorph.trans F
  refine ⟨H, ?_, ?_⟩
  · change (F ∘ R) '' closedBall 0 1 = closedBall 0 1
    rw [image_comp, R.image_closedBall]
    simpa only [map_zero] using hFball
  · intro x
    change F (R (Hemisphere.toSphere hv (Jv x) : E2)) = _
    rw [hRchart, hF _ (sphere_subset_closedBall
      (Hemisphere.toSphere hw (Rp (Jv x))).property)]
    rw [LinearBall.apply_of_mem_sphere L (Hemisphere.toSphere hw (Rp (Jv x))).property]
    change ‖L (Hemisphere.chart hw (Rp (Jv x)) : E2)‖⁻¹ •
      L (Hemisphere.chart hw (Rp (Jv x)) : E2) = _
    rw [Hemisphere.normalized_linear_chart hw L T.toContinuousLinearEquiv
      (Hemisphere.extendLinear_center T.toContinuousLinearEquiv)
      (Hemisphere.extendLinear_plane T.toContinuousLinearEquiv)]
    change (Hemisphere.toSphere hw (Jw (Jv.symm (Rp.symm (Rp (Jv x))))) : E2) = _
    rw [Rp.symm_apply_apply, Jv.symm_apply_apply]

theorem exists_marked_disk_matching
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {r : Real} (hr : 0 < r)
    (f g : E1 → S1)
    (hfi : InjOn f (closedBall 0 r))
    (hfl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x)
    (hgi : InjOn g (closedBall 0 r))
    (hgl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ g x) :
    ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      Q '' (A '' closedBall 0 1) = B '' closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : E1) r, Q (A (f x)) = B (g x) := by
  obtain ⟨Jf, F, hFball, hF⟩ :=
    Compression.exists_marked_arc_round_coordinates hr f hfi hfl
  obtain ⟨Jg, G, hGball, hG⟩ :=
    Compression.exists_marked_arc_round_coordinates hr g hgi hgl
  obtain ⟨H, hHball, hH⟩ := exists_hemisphere_alignment (f 0) (g 0)
    (norm_eq_of_mem_sphere (f 0)) (norm_eq_of_mem_sphere (g 0)) Jf Jg
  let Q := A.symm.trans (F.trans (H.trans (G.symm.trans B)))
  have hGsymm : G.symm '' closedBall 0 1 = closedBall 0 1 := by
    calc
      G.symm '' closedBall 0 1 = G.symm '' (G '' closedBall 0 1) :=
        congrArg (image G.symm) hGball.symm
      _ = closedBall 0 1 := G.toEquiv.symm_image_image _
  have hAsymm : A.symm '' (A '' closedBall 0 1) = closedBall 0 1 :=
    A.toEquiv.symm_image_image _
  refine ⟨Q, ?_, ?_⟩
  · change (B ∘ G.symm ∘ H ∘ F ∘ A.symm) '' (A '' closedBall 0 1) = _
    rw [image_comp, image_comp, image_comp, image_comp,
      hAsymm, hFball, hHball, hGsymm]
  · intro x hx
    change B (G.symm (H (F (A.symm (A (f x)))))) = B (g x)
    rw [A.symm_apply_apply, hF x hx, hH, ← hG x hx, G.symm_apply_apply]

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
