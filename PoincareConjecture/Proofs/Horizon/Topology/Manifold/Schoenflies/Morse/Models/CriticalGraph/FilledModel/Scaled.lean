import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.FilledModel.Height
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.FilledModel.Scaling

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Pointwise

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_ambient_scaled_quadraticMinimum_model
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {r b s : Real}
    (hr : 0 < r) (hb : c + 2 * r ^ 2 < b) (hs : 0 < s) :
    ∃ A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v),
      (∀ x, A x = r • x) ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        F '' sphere (0 : E3) 1 =
          quadraticMinimumCap v c r ∪
            (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
              (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r) ∪
            liftPlaneDiffeomorph hv b s hs.ne' A '' boundedCylinderNorthernCap v := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  let β := (b - c) / r ^ 2 - 2
  have hβ : 0 < β := by
    have hb' : 2 < (b - c) / r ^ 2 := (lt_div_iff₀ hr2).mpr (by linarith)
    dsimp [β]
    linarith
  let σ := s / r ^ 2
  have hσ : 0 < σ := div_pos hs hr2
  obtain ⟨B, hB⟩ := exists_ambient_quadraticMinimum_model_with_upper_scale hv hβ hσ
  let A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v) :=
    (LinearEquiv.smulOfNeZero Real (Hemisphere.Plane v) r hr.ne').toContinuousLinearEquiv.toDiffeomorph
  have hA (x : Hemisphere.Plane v) : A x = r • x := rfl
  let S := liftPlaneDiffeomorph hv (c + 2 * r ^ 2) (r ^ 2) hr2.ne' A
  have hcap : S '' quadraticMinimumCap v (-2) 1 = quadraticMinimumCap v c r :=
    image_quadraticMinimumCap_of_dilation hv c hr A hA
  let ψ : Real → Real := fun t => c + 2 * r ^ 2 + r ^ 2 * t
  have hS (t : Real) (q : Hemisphere.Plane v) :
      S (t • v + (q : E3)) = ψ t • v + (A q : E3) := by
    have he := (heightCoordinates hv).symm_apply_apply (t, q)
    rw [show S (t • v + (q : E3)) = liftPlaneDiffeomorph hv
      (c + 2 * r ^ 2) (r ^ 2) hr2.ne' A (t • v + (q : E3)) from rfl,
      liftPlaneDiffeomorph_apply, show inner Real v (t • v + (q : E3)) = t from
        congrArg Prod.fst he, show (Hemisphere.Plane v).orthogonalProjectionOnto
          (t • v + (q : E3)) = q from congrArg Prod.snd he]
  have hψcont : Continuous ψ := continuous_const.add (continuous_const.mul continuous_id)
  have hψmono : StrictMono ψ := by
    intro x y hxy
    change c + 2 * r ^ 2 + r ^ 2 * x < c + 2 * r ^ 2 + r ^ 2 * y
    linarith [mul_lt_mul_of_pos_left hxy hr2]
  have hinterval : ψ '' Icc (-2 + (7 / 8 : Real) ^ 2) β = Icc (c + (7 * r / 8) ^ 2) b := by
    rw [hψcont.image_Icc_of_strictMono hψmono]
    congr 1 <;> dsimp [ψ, β] <;> field_simp <;> ring
  have hAsphere : A '' sphere (0 : Hemisphere.Plane v) 1 = sphere 0 r := by
    have hAe : (A : Hemisphere.Plane v → Hemisphere.Plane v) = fun x => r • x := funext hA
    rw [hAe]
    change r • sphere (0 : Hemisphere.Plane v) 1 = _
    rw [smul_sphere' hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hcylinder : S ''
      ((fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (-2 + (7 / 8 : Real) ^ 2) β ×ˢ sphere (0 : Hemisphere.Plane v) 1)) =
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
    apply Subset.antisymm
    · rintro y ⟨_, ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩, rfl⟩
      refine ⟨(ψ t, A q), ⟨?_, ?_⟩, (hS t q).symm⟩
      · rw [← hinterval]
        exact ⟨t, ht, rfl⟩
      · rw [← hAsphere]
        exact ⟨q, hq, rfl⟩
    · rintro y ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
      rw [← hinterval] at ht
      rw [← hAsphere] at hq
      obtain ⟨z, hz, rfl⟩ := ht
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨z • v + (x : E3), ⟨(z, x), ⟨hz, hx⟩, rfl⟩, hS z x⟩
  have hupper : S ''
      (liftPlaneDiffeomorph hv β σ hσ.ne'
        (Diffeomorph.refl 𝓘(Real, Hemisphere.Plane v) (Hemisphere.Plane v) ∞) ''
          boundedCylinderNorthernCap v) =
      liftPlaneDiffeomorph hv b s hs.ne' A '' boundedCylinderNorthernCap v := by
    rw [image_image]
    apply image_congr
    intro y _
    change liftPlaneDiffeomorph hv (c + 2 * r ^ 2) (r ^ 2) hr2.ne' A
      (liftPlaneDiffeomorph hv β σ hσ.ne' _ y) = _
    rw [liftPlaneDiffeomorph_apply, inner_liftPlaneDiffeomorph,
      projection_liftPlaneDiffeomorph, liftPlaneDiffeomorph_apply]
    congr 2
    dsimp [β, σ]
    field_simp
    ring
  refine ⟨A, hA, B.trans S, ?_⟩
  change (S ∘ B) '' sphere (0 : E3) 1 = _
  rw [image_comp, hB, image_union, image_union, hcap, hcylinder, hupper]

end Poincare.Manifold.Schoenflies
