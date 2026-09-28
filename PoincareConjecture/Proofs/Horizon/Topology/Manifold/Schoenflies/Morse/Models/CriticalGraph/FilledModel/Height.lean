import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.FilledModel.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.FilledModel.HeightAdjustment

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_ambient_quadraticMinimum_model_with_upper_scale
    {v : E3} (hv : ‖v‖ = 1) {b s : Real} (hb : 0 < b) (hs : 0 < s) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 =
        quadraticMinimumCap v (-2) 1 ∪
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc (-2 + (7 / 8 : Real) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) 1) ∪
          liftPlaneDiffeomorph hv b s hs.ne'
            (Diffeomorph.refl 𝓘(Real, Hemisphere.Plane v) (Hemisphere.Plane v) ∞) ''
              boundedCylinderNorthernCap v := by
  obtain ⟨B, _, hB⟩ := exists_ambient_quadraticMinimum_model hv
  obtain ⟨H, hHmono, hHlow, hHhigh⟩ := exists_quadraticMinimum_height_adjustment hb hs
  let C := (heightCoordinates hv).toDiffeomorph
  let P : (Real × Hemisphere.Plane v) ≃ₘ[Real] (Real × Hemisphere.Plane v) := {
    toEquiv := H.toEquiv.prodCongr (Equiv.refl _)
    contMDiff_toFun := ((H.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff
    contMDiff_invFun := ((H.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff }
  let G := (C.symm.trans P).trans C
  have hG (t : Real) (q : Hemisphere.Plane v) :
      G (t • v + (q : E3)) = H t • v + (q : E3) := by
    change C (P (C.symm (C (t, q)))) = C (H t, q)
    rw [C.symm_apply_apply]
    rfl
  have hGpoint (y : E3) : G y =
      H (inner Real v y) • v + ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) := rfl
  have hGlower (y : E3) (hy : inner Real v y ≤ -1) : G y = y := by
    rw [hGpoint, hHlow _ hy]
    exact (heightCoordinates hv).apply_symm_apply y
  have hcap : G '' quadraticMinimumCap v (-2) 1 = quadraticMinimumCap v (-2) 1 := by
    suffices he : EqOn G id (quadraticMinimumCap v (-2) 1) by
      simpa only [image_id] using image_congr he
    rintro _ ⟨x, hx, rfl⟩
    apply hGlower
    rw [inner_quadraticMinimumCapPoint hv]
    have hn := mem_closedBall_zero_iff.mp hx
    norm_num at hn
    change ‖x‖ ≤ 7 / 8 at hn
    nlinarith [norm_nonneg x]
  have hinterval : H '' Icc (-2 + (7 / 8 : Real) ^ 2) 0 =
      Icc (-2 + (7 / 8 : Real) ^ 2) b := by
    rw [H.continuous.image_Icc_of_strictMono hHmono,
      hHlow _ (by norm_num), hHhigh 0 le_rfl]
    simp
  have hcylinder : G ''
      ((fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (-2 + (7 / 8 : Real) ^ 2) 0 ×ˢ sphere (0 : Hemisphere.Plane v) 1)) =
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (-2 + (7 / 8 : Real) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) 1) := by
    apply Subset.antisymm
    · rintro y ⟨_, ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩, rfl⟩
      refine ⟨(H t, q), ⟨?_, hq⟩, (hG t q).symm⟩
      rw [← hinterval]
      exact ⟨t, ht, rfl⟩
    · rintro y ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
      rw [← hinterval] at ht
      obtain ⟨z, hz, rfl⟩ := ht
      exact ⟨z • v + (q : E3), ⟨(z, q), ⟨hz, hq⟩, rfl⟩, hG z q⟩
  have hupper : G '' boundedCylinderNorthernCap v =
      liftPlaneDiffeomorph hv b s hs.ne'
        (Diffeomorph.refl 𝓘(Real, Hemisphere.Plane v) (Hemisphere.Plane v) ∞) ''
          boundedCylinderNorthernCap v := by
    apply image_congr
    intro y hy
    rw [hGpoint, hHhigh _ (height_nonneg_of_mem_boundedCylinderNorthernCap hy),
      liftPlaneDiffeomorph_apply]
    rfl
  refine ⟨B.trans G, ?_⟩
  change (G ∘ B) '' sphere (0 : E3) 1 = _
  rw [image_comp, hB, image_union, image_union, hcap, hcylinder, hupper]

end Poincare.Manifold.Schoenflies
