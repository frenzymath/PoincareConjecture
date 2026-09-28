import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapInterior
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.SpatialCollarEndpoint
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.EndCapTransport







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

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1




theorem exists_complete_upper_cap_alignment
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    {a c s : Real} (hac : a < c) (hs : 0 < s) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, inner Real v y ≤ a → D y = y) ∧
      (∀ (t : Real) (p : S1), D (t • v + (γ p : E3)) = t • v + (γ p : E3)) ∧
      D '' (liftPlaneDiffeomorph hv c s hs.ne' B '' boundedCylinderNorthernCap v) =
        liftPlaneDiffeomorph hv c s hs.ne' A '' boundedCylinderNorthernCap v := by
  obtain ⟨J, q, ε, hε, hε1, Q, D₁, hD₁height, hD₁lower, hD₁circle, hQcircle,
    hD₁upper, hQgerm⟩ := exists_spatial_collar_alignment_with_constant_endpoint
      hv γ hγ A B hA hB (show a < (a + c) / 2 by linarith)
  let P := ((B.trans Q).trans A.symm)
  have hQimage : Q '' range γ = range γ := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      rw [hQcircle]
      exact mem_range_self p
    · rintro ⟨p, rfl⟩
      exact ⟨γ p, mem_range_self p, hQcircle p⟩
  have hPboundary : P '' sphere (0 : Hemisphere.Plane v) 1 =
      sphere (0 : Hemisphere.Plane v) 1 := by
    change (A.symm ∘ Q ∘ B) '' sphere (0 : Hemisphere.Plane v) 1 = _
    rw [image_comp, image_comp, hB, hQimage, ← hA, ← image_comp]
    have hid : (A.symm ∘ A) = id := funext A.symm_apply_apply
    rw [hid, image_id]
  have hdim : 1 < Module.rank Real (Hemisphere.Plane v) := by
    rw [← Module.finrank_eq_rank, J.toLinearEquiv.finrank_eq]
    norm_num
  let : Nontrivial (Hemisphere.Plane v) := Module.nontrivial_of_finrank_pos
    (R := Real) (by rw [J.toLinearEquiv.finrank_eq]; norm_num)
  have hPball : P '' ball (0 : Hemisphere.Plane v) 1 = ball (0 : Hemisphere.Plane v) 1 := by
    simpa using P.toHomeomorph.image_ball_eq_of_image_sphere_eq
      (Homeomorph.refl _) hdim (by simpa using hPboundary)
  have hPnorm (x : Hemisphere.Plane v) (hx : |‖x‖ - 1| < ε) : ‖P x‖ = ‖x‖ := by
    have hx0 : 0 < ‖x‖ := by have := (abs_lt.mp hx).1; linarith
    let p : S1 := ⟨‖x‖⁻¹ • J x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hx0), J.norm_map, inv_mul_cancel₀ hx0.ne']⟩
    have hrep : ‖x‖ • J.symm (p : E2) = x := by
      apply J.injective
      rw [map_smul, J.apply_symm_apply]
      change ‖x‖ • (‖x‖⁻¹ • J x) = J x
      rw [smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]
    have hg := hQgerm (q.symm p) ‖x‖ hx
    rw [q.apply_symm_apply, hrep] at hg
    have hp : P x = ‖x‖ • J.symm (q.symm p : E2) := by
      change A.symm (Q (B x)) = _
      rw [hg, A.symm_apply_apply]
    rw [hp, norm_smul, Real.norm_eq_abs, abs_of_pos hx0, J.symm.norm_map]
    simp
  obtain ⟨K, hK, hKO, H, hHproj, hHfix, hHcap⟩ :=
    exists_upper_cap_interior_normalization hv P hPball hPboundary hε hε1 hPnorm
  let L := liftPlaneDiffeomorph hv c s hs.ne' A
  let D₂ := (L.symm.trans H).trans L
  have hD₂fix (y : E3) (hy : L.symm y ∉ K) : D₂ y = y := by
    change L (H (L.symm y)) = y
    rw [hHfix _ hy, L.apply_symm_apply]
  have hD₂lower (y : E3) (hy : inner Real v y ≤ c) : D₂ y = y := by
    apply hD₂fix
    intro h
    have hp := (hKO h).1
    have he := inner_liftPlaneDiffeomorph hv c s hs.ne' A (L.symm y)
    change inner Real v (L (L.symm y)) = _ at he
    rw [L.apply_symm_apply] at he
    nlinarith
  have hD₂circle (t : Real) (p : S1) : D₂ (t • v + (γ p : E3)) = t • v + (γ p : E3) := by
    apply hD₂fix
    intro h
    have hn := (hKO h).2
    have hγp : γ p ∈ A '' sphere (0 : Hemisphere.Plane v) 1 := by
      rw [hA]; exact mem_range_self p
    obtain ⟨x, hx, hxp⟩ := hγp
    have hproj : (Hemisphere.Plane v).orthogonalProjectionOnto
        (L.symm (t • v + (γ p : E3))) = x := by
      apply A.injective
      have he := projection_liftPlaneDiffeomorph hv c s hs.ne' A
        (L.symm (t • v + (γ p : E3)))
      change (Hemisphere.Plane v).orthogonalProjectionOnto (L (L.symm _)) = _ at he
      rw [L.apply_symm_apply] at he
      have hp := congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply (t, γ p))
      change (Hemisphere.Plane v).orthogonalProjectionOnto (t • v + (γ p : E3)) = γ p at hp
      rw [hp] at he
      exact he.symm.trans hxp.symm
    rw [hproj, mem_sphere_zero_iff_norm.mp hx] at hn
    exact (lt_irrefl 1) hn
  have hcompose (y : E3) : L (liftPlaneDiffeomorph hv 0 1 one_ne_zero P y) =
      liftPlaneDiffeomorph hv c s hs.ne' (B.trans Q) y := by
    rw [liftPlaneDiffeomorph_apply]
    change (c + s * inner Real v (liftPlaneDiffeomorph hv 0 1 one_ne_zero P y)) • v +
      (A ((Hemisphere.Plane v).orthogonalProjectionOnto
        (liftPlaneDiffeomorph hv 0 1 one_ne_zero P y)) : E3) = _
    rw [inner_liftPlaneDiffeomorph, projection_liftPlaneDiffeomorph,
      zero_add, one_mul, liftPlaneDiffeomorph_apply]
    change (c + s * inner Real v y) • v + (A (A.symm (Q (B _))) : E3) = _
    rw [A.apply_symm_apply]
    rfl
  have hD₂cap : D₂ '' (liftPlaneDiffeomorph hv c s hs.ne' (B.trans Q) ''
      boundedCylinderNorthernCap v) = L '' boundedCylinderNorthernCap v := by
    have heq : liftPlaneDiffeomorph hv c s hs.ne' (B.trans Q) '' boundedCylinderNorthernCap v =
        L '' (liftPlaneDiffeomorph hv 0 1 one_ne_zero P '' boundedCylinderNorthernCap v) := by
      rw [image_image]
      apply image_congr
      intro y _
      exact (hcompose y).symm
    rw [heq, image_image]
    change (fun y => L (H (L.symm (L y)))) ''
      (liftPlaneDiffeomorph hv 0 1 one_ne_zero P '' boundedCylinderNorthernCap v) = _
    simp only [L.symm_apply_apply]
    rw [← image_image, hHcap]
  refine ⟨D₁.trans D₂, ?_, ?_, ?_⟩
  · intro y hy
    change D₂ (D₁ y) = y
    rw [hD₁lower y hy, hD₂lower y (hy.trans hac.le)]
  · intro t p
    change D₂ (D₁ (t • v + (γ p : E3))) = _
    rw [hD₁circle, hD₂circle]
  · change (D₂ ∘ D₁) '' _ = _
    rw [image_comp, image_upper_cap_of_constant_plane_action hv
      (show (a + c) / 2 ≤ c by linarith) hs B Q D₁ hD₁upper, hD₂cap]

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
