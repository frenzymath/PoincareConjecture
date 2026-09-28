import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapAlignment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

theorem exists_smooth_circle_parametrization_of_plane_filling
    {v : E3} (hv : ‖v‖ = 1)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    ∃ γ : S1 → Hemisphere.Plane v,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ ∧
      A '' sphere (0 : Hemisphere.Plane v) 1 = range γ := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro h; simp [h] at hv)).repr
  let j := J.symm.toContinuousLinearEquiv.toDiffeomorph.trans A
  let γ : S1 → Hemisphere.Plane v := fun p => j p
  have hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ := by
    apply isSmoothEmbedding_of_injective_mfderiv
      (j.contMDiff.comp (fun p => contMDiff_coe_sphere (n := 1) p))
      (j.injective.comp Subtype.val_injective)
    intro p
    change Injective (mfderiv (𝓡 1) 𝓘(Real, Hemisphere.Plane v)
      (j ∘ fun p : S1 => (p : E2)) p)
    rw [mfderiv_comp p (j.contMDiff.mdifferentiable (by simp) _)
      ((contMDiff_coe_sphere (n := 1) (m := ∞) p).mdifferentiableAt (by simp))]
    exact (j.mfderivToContinuousLinearEquiv (by simp) (p : E2)).injective.comp
      (by convert! injective_mvfderiv_subtypeVal_sphere (n := 1) p)
  refine ⟨γ, hγ, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨J y, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, J.norm_map]
      exact mem_sphere_zero_iff_norm.mp hy
    · change A (J.symm (J y)) = A y
      rw [J.symm_apply_apply]
  · rintro ⟨p, rfl⟩
    refine ⟨J.symm p, ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm, J.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp p.property

theorem exists_ambient_capped_cylinder_of_two_fillings
    {v : E3} (hv : ‖v‖ = 1) (a b : Real) (hab : a < b)
    (u w : Real) (hu : 0 < u) (hw : 0 < w)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 =
      B '' sphere (0 : Hemisphere.Plane v) 1) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 =
        (liftPlaneDiffeomorph hv a (-u) (neg_ne_zero.mpr hu.ne') A ''
          boundedCylinderNorthernCap v) ∪
        ((fun z : Real × Hemisphere.Plane v => z.1 • v + (A z.2 : E3)) ''
          (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) 1)) ∪
        (liftPlaneDiffeomorph hv b w hw.ne' B '' boundedCylinderNorthernCap v) := by
  obtain ⟨γ, hγ, hA⟩ := exists_smooth_circle_parametrization_of_plane_filling hv A
  have hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ := hboundary.symm.trans hA
  obtain ⟨D, hDlow, hDcyl, hDcap⟩ :=
    exists_complete_upper_cap_alignment hv γ hγ A B hA hB hab hw
  obtain ⟨F, hF⟩ := exists_ambient_capped_cylinder_of_scales hv a b hab.le u w hu hw A
  let L := liftPlaneDiffeomorph hv a (-u) (neg_ne_zero.mpr hu.ne') A ''
    boundedCylinderNorthernCap v
  let C := (fun z : Real × Hemisphere.Plane v => z.1 • v + (A z.2 : E3)) ''
    (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) 1)
  have hDL : D '' L = L :=
    image_lower_cap_of_fixed_lower_halfSpace hv le_rfl hu A D hDlow
  have hDC : D '' C = C := by
    calc
      D '' C = id '' C := by
        apply image_congr
        rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
        have hmem : A x ∈ range γ := by rw [← hA]; exact ⟨x, hx, rfl⟩
        obtain ⟨p, hp⟩ := hmem
        change D (t • v + (A x : E3)) = t • v + (A x : E3)
        rw [← hp]
        exact hDcyl t p
      _ = C := image_id _
  refine ⟨F.trans D.symm, ?_⟩
  apply D.injective.image_injective
  change D '' ((D.symm ∘ F) '' sphere (0 : E3) 1) = D '' _
  rw [image_comp, image_image]
  simp only [D.apply_symm_apply]
  rw [image_union, image_union, hDL, hDC, hDcap]
  simpa only [image_id', L, C, boundedCylinderNorthernCap] using hF

end Poincare.Manifold.Schoenflies
