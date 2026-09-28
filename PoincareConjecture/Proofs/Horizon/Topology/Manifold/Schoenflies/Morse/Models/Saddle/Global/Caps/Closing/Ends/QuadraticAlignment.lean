import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.FilledModel.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Physical



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean
open Saddle.Wall.Smoothing.Exterior.Caps

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩



theorem exists_relative_radial_lower_cap_transport
    {v : E3} (hv : ‖v‖ = 1) (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
    (r₀ r₁ : S2 → Real)
    (hr₀ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ r₀)
    (hr₁ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ r₁)
    (hpos₀ : ∀ p, 0 < r₀ p) (hpos₁ : ∀ p, 0 < r₁ p)
    {ε : Real} (hε : 0 < ε)
    (heq : ∀ p : S2, inner Real v (p : E3) ∈ Icc (-ε) 0 → r₀ p = r₁ p) :
    ∃ (η : Real) (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ (∀ x, -η ≤ inner Real v x → F x = x) ∧
      (∃ K : Set E3, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      ∀ p : S2, inner Real v (p : E3) ≤ 0 →
        F (r₀ p • (p : E3)) = r₁ p • (p : E3) := by
  let R := (Hemisphere.Plane v).reflection
  have hRh (x : E3) : inner Real v (R x) = -inner Real v x := by
    have hR : R x = x - (2 * inner Real v x) • v := by
      change (Real ∙ v)ᗮ.reflection x = _
      rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, hv]
      module
    rw [hR]
    simp [inner_sub_right, inner_smul_right, hv]
    ring
  let P := (capPhysicalFrame hv J).trans R.toContinuousLinearEquiv.toDiffeomorph
  have hPn (x : E3) : ‖P x‖ = ‖x‖ := by
    change ‖R (capPhysicalFrame hv J x)‖ = _
    rw [R.norm_map, capPhysicalFrame_norm]
  have hPh (x : E3) : inner Real v (P x) = -x 2 := by
    change inner Real v (R (capPhysicalFrame hv J x)) = _
    rw [hRh, capPhysicalFrame_height]
  have hPs (s : Real) (x : E3) : P (s • x) = s • P x := by
    change R (capPhysicalFrame hv J (s • x)) = _
    rw [capPhysicalFrame_smul, map_smul]
    rfl
  let f : S2 → S2 := fun p => ⟨P p, by rw [mem_sphere_zero_iff_norm, hPn, norm_eq_of_mem_sphere]⟩
  have hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f :=
    (P.contMDiff.comp (fun p => contMDiff_coe_sphere (n := 2) p)).codRestrict_sphere _
  obtain ⟨η, E, hη, hfix, ⟨K, hK, hKfix⟩, hmap⟩ :=
    exists_relative_radial_upper_cap_transport (r₀ ∘ f) (r₁ ∘ f)
      (hr₀.comp hf) (hr₁.comp hf) (fun p => hpos₀ (f p)) (fun p => hpos₁ (f p)) hε
      (fun p hp => heq (f p) (by change inner Real v (P p) ∈ _; rw [hPh]; constructor <;> linarith [hp.1, hp.2]))
  let F := (P.symm.trans E).trans P
  refine ⟨η, F, hη, ?_, ⟨P '' K, hK.image P.continuous, ?_⟩, ?_⟩
  · intro x hx
    have hh := hPh (P.symm x)
    rw [P.apply_symm_apply] at hh
    change P (E (P.symm x)) = x
    rw [hfix _ (by linarith), P.apply_symm_apply]
  · intro x hx
    have hn : P.symm x ∉ K := fun h => hx ⟨P.symm x, h, P.apply_symm_apply x⟩
    change P (E (P.symm x)) = x
    rw [hKfix _ hn, P.apply_symm_apply]
  · intro p hp
    let q : S2 := ⟨P.symm p, by
      rw [mem_sphere_zero_iff_norm, ← hPn, P.apply_symm_apply, norm_eq_of_mem_sphere]⟩
    have hfp : f q = p := Subtype.ext (P.apply_symm_apply p)
    have hh := hPh q
    have hPq : P q = p := P.apply_symm_apply p
    rw [hPq] at hh
    have hm := hmap q (by linarith)
    simp only [Function.comp_apply, hfp] at hm
    have hpre : P.symm (r₀ p • (p : E3)) = r₀ p • (q : E3) := by
      apply P.injective
      change P (P.symm (r₀ p • (p : E3))) = P (r₀ p • (q : E3))
      rw [P.apply_symm_apply, hPs, hPq]
    change P (E (P.symm (r₀ p • (p : E3)))) = _
    rw [hpre, hm, hPs, hPq]



theorem exists_relative_quadratic_lower_profile_transport
    {v : E3} (hv : ‖v‖ = 1) (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2) :
    ∃ (η : Real) (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ (∀ x, -η ≤ inner Real v x → F x = x) ∧
      (∃ K : Set E3, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      F '' quadraticMinimumLowerSurface v =
        (fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p | inner Real v (p : E3) ≤ 0} := by
  obtain ⟨η, F, hη, hfix, hsupport, hmap⟩ :=
    exists_relative_radial_lower_cap_transport hv J
      (quadraticMinimumRadius v) (boundedCylinderRadius v)
      (contMDiff_quadraticMinimumRadius hv) (contMDiff_boundedCylinderRadius v)
      (quadraticMinimumRadius_pos hv) (boundedCylinderRadius_pos v)
      (show (0 : Real) < 1 / 4 by norm_num) (fun p hp => by
        rw [quadraticMinimumRadius_eq_cylinder p ⟨by linarith [hp.1], by linarith [hp.2]⟩,
          boundedCylinderRadius_of_abs_height_le v p (abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩)])
  refine ⟨η, F, hη, hfix, hsupport, ?_⟩
  rw [← image_quadraticMinimum_south_eq_lower hv, image_image]
  exact image_congr hmap

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
