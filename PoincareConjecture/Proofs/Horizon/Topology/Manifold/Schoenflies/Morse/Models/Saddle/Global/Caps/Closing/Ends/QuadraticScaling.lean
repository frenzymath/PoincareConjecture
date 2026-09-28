import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.QuadraticAlignment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.FilledModel.Scaling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.TwoCaps



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology Pointwise

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem image_south_radial_cap_of_lift
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v)) :
    liftPlaneDiffeomorph hv c s hs A ''
      ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
        {p | inner Real v (p : E3) ≤ 0}) =
    liftPlaneDiffeomorph hv c (-s) (neg_ne_zero.mpr hs) A ''
      boundedCylinderNorthernCap v := by
  let R := (Hemisphere.Plane v).reflection
  have hR (x : E3) : R x = x - (2 * inner Real v x) • v := by
    change (Real ∙ v)ᗮ.reflection x = _
    rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, hv]
    module
  have hRh (x : E3) : inner Real v (R x) = -inner Real v x := by
    rw [hR]
    simp [inner_sub_right, inner_smul_right, hv]
    ring
  have hRp (x : E3) : (Hemisphere.Plane v).orthogonalProjectionOnto (R x) =
      (Hemisphere.Plane v).orthogonalProjectionOnto x := by
    rw [hR]
    simp [Hemisphere.Plane]
  let ρ : S2 → S2 := fun p => ⟨R p, by
    rw [mem_sphere_zero_iff_norm, R.norm_map, norm_eq_of_mem_sphere]⟩
  let β : S2 → E3 := fun p => boundedCylinderRadius v p • (p : E3)
  have hρh (p : S2) : inner Real v (ρ p : E3) = -inner Real v (p : E3) := hRh p
  have hβρ (p : S2) : β (ρ p) = R (β p) := by
    have heq : boundedCylinderRadius v (ρ p) = boundedCylinderRadius v p :=
      boundedCylinderRadius_eq_of_sq_height_eq v (by rw [hρh, neg_sq])
    change boundedCylinderRadius v (ρ p) • R (p : E3) = R (boundedCylinderRadius v p • p)
    rw [heq, map_smul]
  have hpoint (p : S2) : liftPlaneDiffeomorph hv c s hs A (β (ρ p)) =
      liftPlaneDiffeomorph hv c (-s) (neg_ne_zero.mpr hs) A (β p) := by
    rw [hβρ, liftPlaneDiffeomorph_apply, liftPlaneDiffeomorph_apply, hRh, hRp]
    congr 2
    ring
  ext y
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    change inner Real v (p : E3) ≤ 0 at hp
    refine ⟨β (ρ p), ⟨ρ p, by change 0 ≤ inner Real v (ρ p : E3); rw [hρh]; linarith, rfl⟩, ?_⟩
    have hρρ : ρ (ρ p) = p := Subtype.ext ((Hemisphere.Plane v).reflection_reflection p)
    simpa only [hρρ] using (hpoint (ρ p)).symm
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    change 0 ≤ inner Real v (p : E3) at hp
    exact ⟨β (ρ p), ⟨ρ p, by change inner Real v (ρ p : E3) ≤ 0; rw [hρh]; linarith, rfl⟩,
      hpoint p⟩




theorem exists_relative_scaled_quadratic_lower_transport
    {v : E3} (hv : ‖v‖ = 1) (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
    (c : Real) {r b : Real} (hr : 0 < r) (hb : c + 2 * r ^ 2 < b) :
    ∃ A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v),
      (∀ x, A x = r • x) ∧
      ∃ η : Real, 0 < η ∧ ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, c + 2 * r ^ 2 - η ≤ inner Real v y → F y = y) ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F y = y) ∧
        F '' (quadraticMinimumCap v c r ∪
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r)) =
          (liftPlaneDiffeomorph hv (c + 2 * r ^ 2) (-(r ^ 2))
            (neg_ne_zero.mpr (sq_pos_of_pos hr).ne') A '' boundedCylinderNorthernCap v) ∪
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc (c + 2 * r ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  let A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v) :=
    (LinearEquiv.smulOfNeZero Real (Hemisphere.Plane v) r hr.ne').toContinuousLinearEquiv.toDiffeomorph
  have hA (x : Hemisphere.Plane v) : A x = r • x := rfl
  let d := c + 2 * r ^ 2
  let S := liftPlaneDiffeomorph hv d (r ^ 2) hr2.ne' A
  let ψ : Real → Real := fun t => d + r ^ 2 * t
  have hS (t : Real) (q : Hemisphere.Plane v) :
      S (t • v + (q : E3)) = ψ t • v + (A q : E3) := by
    have he := (heightCoordinates hv).symm_apply_apply (t, q)
    rw [show S (t • v + (q : E3)) = liftPlaneDiffeomorph hv d (r ^ 2) hr2.ne' A
      (t • v + (q : E3)) from rfl, liftPlaneDiffeomorph_apply,
      show inner Real v (t • v + (q : E3)) = t from congrArg Prod.fst he,
      show (Hemisphere.Plane v).orthogonalProjectionOnto (t • v + (q : E3)) = q from
        congrArg Prod.snd he]
  have hAsphere : A '' sphere (0 : Hemisphere.Plane v) 1 = sphere 0 r := by
    rw [show (A : Hemisphere.Plane v → Hemisphere.Plane v) = (fun x => r • x) from funext hA]
    change r • sphere (0 : Hemisphere.Plane v) 1 = _
    rw [smul_sphere' hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hψcont : Continuous ψ := continuous_const.add (continuous_const.mul continuous_id)
  have hψmono : StrictMono ψ := by
    intro x y hxy
    dsimp [ψ]
    linarith [mul_lt_mul_of_pos_left hxy hr2]
  have hinterval : ψ '' Icc (-2 + (7 / 8 : Real) ^ 2) 0 = Icc (c + (7 * r / 8) ^ 2) d := by
    rw [hψcont.image_Icc_of_strictMono hψmono]
    congr 1 <;> dsimp [ψ, d] <;> ring
  have hcylinder : S ''
      ((fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (-2 + (7 / 8 : Real) ^ 2) 0 ×ˢ sphere (0 : Hemisphere.Plane v) 1)) =
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (c + (7 * r / 8) ^ 2) d ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩, rfl⟩
      refine ⟨(ψ t, A q), ⟨?_, ?_⟩, (hS t q).symm⟩
      · rw [← hinterval]; exact mem_image_of_mem ψ ht
      · rw [← hAsphere]; exact mem_image_of_mem A hq
    · rintro _ ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
      rw [← hinterval] at ht
      rw [← hAsphere] at hq
      obtain ⟨z, hz, rfl⟩ := ht
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨z • v + (x : E3), ⟨(z, x), ⟨hz, hx⟩, rfl⟩, hS z x⟩
  have hscaled : S '' quadraticMinimumLowerSurface v = quadraticMinimumCap v c r ∪
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (c + (7 * r / 8) ^ 2) d ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
    rw [quadraticMinimumLowerSurface_eq_cap_union_cylinder hv, image_union,
      image_quadraticMinimumCap_of_dilation hv c hr A hA, hcylinder]
  obtain ⟨η, F₀, hη, hfix, ⟨K, hK, hKfix⟩, hmap⟩ :=
    exists_relative_quadratic_lower_profile_transport hv J
  let F := (S.symm.trans F₀).trans S
  have hFfix (y : E3) (hy : d - r ^ 2 * η ≤ inner Real v y) : F y = y := by
    have hheight := inner_liftPlaneDiffeomorph hv d (r ^ 2) hr2.ne' A (S.symm y)
    change inner Real v (S (S.symm y)) = _ at hheight
    rw [S.apply_symm_apply] at hheight
    change S (F₀ (S.symm y)) = y
    rw [hfix _ (by nlinarith), S.apply_symm_apply]
  let tail := (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
    (Icc d b ×ˢ sphere (0 : Hemisphere.Plane v) r)
  have htail : F '' tail = tail := by
    calc
      _ = id '' tail := by
        apply image_congr
        rintro _ ⟨⟨t, q⟩, ⟨ht, _⟩, rfl⟩
        apply hFfix
        have hh := congrArg Prod.fst ((heightCoordinates hv).symm_apply_apply (t, q))
        change inner Real v (t • v + (q : E3)) = t at hh
        rw [hh]
        nlinarith [ht.1]
      _ = _ := image_id _
  have hsource : quadraticMinimumCap v c r ∪
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r) =
      S '' quadraticMinimumLowerSurface v ∪ tail := by
    rw [hscaled, union_assoc, ← image_union, ← union_prod,
      Icc_union_Icc_eq_Icc (show c + (7 * r / 8) ^ 2 ≤ d by dsimp [d]; nlinarith) hb.le]
  refine ⟨A, hA, r ^ 2 * η, mul_pos hr2 hη, F, hFfix,
    ⟨S '' K, hK.image S.continuous, ?_⟩, ?_⟩
  · intro y hy
    have hnot : S.symm y ∉ K := fun h => hy ⟨S.symm y, h, S.apply_symm_apply y⟩
    change S (F₀ (S.symm y)) = y
    rw [hKfix _ hnot, S.apply_symm_apply]
  · rw [hsource, image_union, htail]
    congr 1
    simp only [F, Diffeomorph.coe_trans, image_image, Function.comp_apply, S.symm_apply_apply]
    change (S ∘ F₀) '' quadraticMinimumLowerSurface v = _
    rw [image_comp, hmap]
    exact image_south_radial_cap_of_lift hv d (r ^ 2) hr2.ne' A

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
