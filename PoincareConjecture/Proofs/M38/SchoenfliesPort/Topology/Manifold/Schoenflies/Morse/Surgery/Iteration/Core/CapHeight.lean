import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Caps
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.Hyperplane

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

open Poincare.Geometry.Euclidean

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E2 = 1+1) := ⟨by simp⟩
private instance : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
  (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) (0 : E2) zero_le_one)

variable {v : E3} {g : S2 → E3} {B : Set Real}

theorem normalized_height_nonneg (D : SphereSurgeryCoreCap v g B)
    {x : E2} (hx : x ∈ closedBall (0 : E2) 1) :
    0 ≤ (inner Real v (D.parametrization x)-D.center)/D.scale := by
  have hm := D.range_eq ▸ mem_image_of_mem D.parametrization hx
  obtain ⟨y, hy, hxy⟩ := hm
  rw [← hxy, inner_liftPlaneDiffeomorph, add_sub_cancel_left,
    mul_div_cancel_left₀ _ D.scale_ne_zero]
  exact height_nonneg_of_mem_boundedCylinderNorthernCap hy

theorem zero_slice_eq_circle (D : SphereSurgeryCoreCap v g B) :
    (D.parametrization '' closedBall (0 : E2) 1) ∩
      {y : E3 | inner Real v y = D.center} =
        (fun x : Hemisphere.Plane v => D.center • v + (D.planeMap x : E3)) ''
          sphere (0 : Hemisphere.Plane v) 1 := by
  rw [D.range_eq]
  simpa only [boundedCylinderNorthernCap, mul_zero, add_zero] using
    lifted_cap_slice_eq_circle D.unit_v D.center D.scale D.scale_ne_zero D.planeMap
      (show (0 : Real) ∈ Ico 0 1 by norm_num)

theorem boundary_image_eq_circle (D : SphereSurgeryCoreCap v g B) :
    D.parametrization '' sphere (0 : E2) 1 =
      (fun x : Hemisphere.Plane v => D.center • v + (D.planeMap x : E3)) ''
        sphere (0 : Hemisphere.Plane v) 1 := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simpa [heq] using D.unit_v)).repr
  let γ : S1 → E3 := fun q => D.parametrization q
  have hγ : ContMDiff (𝓡 1) (𝓡 3) ∞ γ :=
    D.parametrization_smooth.contMDiff.comp (contMDiff_coe_sphere (n := 1))
  have hheight (q : S1) : inner Real v (γ q) = D.center := D.boundary_height q q.property
  have hγinj (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) γ q) := by
    change Injective (mfderiv (𝓡 1) (𝓡 3)
      (D.parametrization ∘ (Subtype.val : S1 → E2)) q)
    rw [mfderiv_comp q
      ((D.parametrization_smooth.contMDiff (q : E2)).mdifferentiableAt (by simp))
      (((contMDiff_coe_sphere (n := 1) (m := ∞)) q).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
    apply (D.parametrization_deriv_injective q).comp
    convert! injective_mvfderiv_subtypeVal_sphere q
  let Q : S1 → E2 := fun q => J (D.planeMap.symm
    ((Hemisphere.Plane v).orthogonalProjectionOnto (γ q)))
  have hQ : ContMDiff (𝓡 1) (𝓡 2) ∞ Q :=
    J.toContinuousLinearEquiv.contDiff.contMDiff.comp
      (D.planeMap.symm.contMDiff.comp
        ((Hemisphere.Plane v).orthogonalProjectionOnto.contMDiff.comp hγ))
  have hQmem (q : S1) : Q q ∈ sphere (0 : E2) 1 := by
    have hm : γ q ∈ (fun x : Hemisphere.Plane v =>
        D.center • v + (D.planeMap x : E3)) '' sphere (0 : Hemisphere.Plane v) 1 := by
      rw [← D.zero_slice_eq_circle]
      exact ⟨mem_image_of_mem D.parametrization (sphere_subset_closedBall q.property), hheight q⟩
    obtain ⟨z, hz, hzq⟩ := hm
    have hQq : Q q = J z := by
      change J (D.planeMap.symm ((Hemisphere.Plane v).orthogonalProjectionOnto (γ q))) = _
      rw [← hzq]
      simp [Hemisphere.Plane,
        Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
    rw [hQq, mem_sphere_zero_iff_norm, J.norm_map]
    exact mem_sphere_zero_iff_norm.mp hz
  let C : S1 → S1 := fun q => ⟨Q q, hQmem q⟩
  have hC : ContMDiff (𝓡 1) (𝓡 1) ∞ C := hQ.codRestrict_sphere hQmem
  let L : S1 → E3 := fun q => D.center • v + (D.planeMap (J.symm (q : E2)) : E3)
  have hL : ContMDiff (𝓡 1) (𝓡 3) ∞ L :=
    contMDiff_const.add ((Hemisphere.Plane v).subtypeL.contMDiff.comp
      (D.planeMap.contMDiff.comp (J.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
        (contMDiff_coe_sphere (n := 1)))))
  have hfactor : γ = L ∘ C := by
    funext q
    change γ q = D.center • v + (D.planeMap (J.symm
      (J (D.planeMap.symm ((Hemisphere.Plane v).orthogonalProjectionOnto (γ q))))) : E3)
    rw [J.symm_apply_apply, D.planeMap.apply_symm_apply]
    exact Poincare.Geometry.Manifold.eq_height_smul_add_projection D.unit_v hheight q
  have hbij (q : S1) : Bijective (mfderiv (𝓡 1) (𝓡 1) C q) := by
    have hchain := mfderiv_comp q ((hL (C q)).mdifferentiableAt (by simp))
      ((hC q).mdifferentiableAt (by simp))
    rw [← hfactor] at hchain
    have hinj : Injective (mfderiv (𝓡 1) (𝓡 1) C q) := by
      intro u w huw
      apply hγinj q
      rw [hchain]
      exact congrArg (mfderiv (𝓡 1) (𝓡 3) L (C q)) huw
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E1) (V₂ := E1) (f := (mfderiv (𝓡 1) (𝓡 1) C q).toLinearMap) rfl).mp hinj⟩
  have hsurj := Poincare.Geometry.Manifold.surjective_of_compact_of_bijective_mfderiv hC hbij
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [← D.zero_slice_eq_circle]
    exact ⟨mem_image_of_mem D.parametrization (sphere_subset_closedBall hx), D.boundary_height x hx⟩
  · rintro y ⟨z, hz, rfl⟩
    let q : S1 := ⟨J z, by simpa only [mem_sphere_zero_iff_norm, J.norm_map] using hz⟩
    obtain ⟨p, hp⟩ := hsurj q
    refine ⟨(p : E2), p.property, ?_⟩
    change γ p = _
    rw [hfactor]
    change L (C p) = _
    rw [hp]
    change D.center • v + (D.planeMap (J.symm (J z)) : E3) = _
    rw [J.symm_apply_apply]

theorem normalized_height_eq_zero_iff (D : SphereSurgeryCoreCap v g B)
    {x : E2} (hx : x ∈ closedBall (0 : E2) 1) :
    (inner Real v (D.parametrization x)-D.center)/D.scale = 0 ↔
      x ∈ sphere (0 : E2) 1 := by
  constructor
  · intro hz
    have hh : inner Real v (D.parametrization x) = D.center := by
      have := (div_eq_zero_iff).mp hz
      exact sub_eq_zero.mp (this.resolve_right D.scale_ne_zero)
    have hm : D.parametrization x ∈ D.parametrization '' sphere (0 : E2) 1 := by
      rw [D.boundary_image_eq_circle, ← D.zero_slice_eq_circle]
      exact ⟨mem_image_of_mem D.parametrization hx, hh⟩
    obtain ⟨y, hy, hxy⟩ := hm
    exact D.parametrization_injective hxy ▸ hy
  · intro hxS
    rw [D.boundary_height x hxS, sub_self, zero_div]

theorem normalized_height_pos (D : SphereSurgeryCoreCap v g B)
    {x : E2} (hx : x ∈ ball (0 : E2) 1) :
    0 < (inner Real v (D.parametrization x)-D.center)/D.scale := by
  apply lt_of_le_of_ne (D.normalized_height_nonneg (ball_subset_closedBall hx))
  intro hz
  have hS := (D.normalized_height_eq_zero_iff (ball_subset_closedBall hx)).mp hz.symm
  have hn := mem_sphere_zero_iff_norm.mp hS
  have hlt := mem_ball_zero_iff.mp hx
  linarith

theorem normalized_height_pos_on_open_disk (D : SphereSurgeryCoreCap v g B)
    {p : S2} (hp : p ∈ D.chart '' ball (0 : E2) 1) :
    0 < (inner Real v (g p)-D.center)/D.scale := by
  obtain ⟨x, hx, rfl⟩ := hp
  rw [D.parametrization_eq x (ball_subset_closedBall hx)]
  exact D.normalized_height_pos hx

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
