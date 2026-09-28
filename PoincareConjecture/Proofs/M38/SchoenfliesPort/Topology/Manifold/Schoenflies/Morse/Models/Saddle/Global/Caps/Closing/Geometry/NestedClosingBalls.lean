import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ClosingBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.CylinderInterior
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.SeparatedClosures

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)

private theorem cylinder_circle_image {v : E3}
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v)) (a b : Real) :
    terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b =
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (A z.2 : E3)) ''
        (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) 1) := by
  rw [terminalCylinder_eq_height_product]
  ext y
  constructor
  · rintro ⟨⟨t, x⟩, ⟨ht, ⟨q, hq, rfl⟩⟩, rfl⟩
    exact ⟨(t, q), ⟨ht, hq⟩, rfl⟩
  · rintro ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
    exact ⟨(t, A q), ⟨ht, mem_image_of_mem A hq⟩, rfl⟩

private theorem closing_cap_rim_subset
    {v : E3} (hv : ‖v‖ = 1)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {a b s w : Real} (hab : a ≤ b) (hs : s < 0) (hw : 0 < w)
    (N Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN : EqOn N Q {y | b ≤ inner Real v y}) {E : Set E3}
    (himage : N '' E =
      liftPlaneDiffeomorph hv a s hs.ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b)
    {y : E3}
    (hy : y ∈ Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v))
    (hh : inner Real v y = b) : y ∈ E := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hzheight : inner Real v z = b := by
    rw [← Q.apply_symm_apply z, hQ]
    exact hh
  have hrim : z ∈ (fun x : Hemisphere.Plane v => b • v + (A x : E3)) '' sphere 0 1 := by
    have hslice := lifted_cap_slice_eq_circle hv b w hw.ne' A
      (show (0 : Real) ∈ Ico 0 1 by constructor <;> norm_num)
    simp only [mul_zero, add_zero] at hslice
    rw [← hslice]
    exact ⟨hz, hzheight⟩
  have hzN : z ∈ N '' E := by
    rw [himage]
    apply Or.inr
    rw [cylinder_circle_image]
    obtain ⟨x, hx, rfl⟩ := hrim
    exact ⟨(b, x), ⟨⟨hab, le_rfl⟩, hx⟩, rfl⟩
  obtain ⟨x, hx, heq⟩ := hzN
  have heq' : N (Q.symm z) = z := by
    rw [hN (by change b ≤ inner Real v (Q.symm z); exact hh.ge), Q.apply_symm_apply]
  exact (N.injective (heq.trans heq'.symm)) ▸ hx

theorem exists_strictly_nested_curved_closing_balls
    {v : E3} (hv : ‖v‖ = 1)
    (A B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {a d b s t u w : Real} (hab : a ≤ b) (hdb : d ≤ b)
    (hs : s < 0) (ht : t < 0) (hu : 0 < u) (hw : 0 < w)
    (hAB : A '' closedBall 0 1 ⊆ B '' ball 0 1) (hscale : 2 * u < w)
    (N₁ N₂ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN₁ : EqOn N₁ Q {y | b ≤ inner Real v y})
    (hN₂ : EqOn N₂ Q {y | b ≤ inner Real v y})
    {E M : Set E3} (hEM : Disjoint E M)
    (hEheight : ∀ y ∈ E, inner Real v y ≤ b)
    (hMheight : ∀ y ∈ M, inner Real v y ≤ b)
    (hE : N₁ '' E = liftPlaneDiffeomorph hv a s hs.ne A '' boundedCylinderNorthernCap v ∪
      terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b)
    (hM : N₂ '' M = liftPlaneDiffeomorph hv d t ht.ne B '' boundedCylinderNorthernCap v ∪
      terminalCylinder (B '' sphere (0 : Hemisphere.Plane v) 1) d b) :
    ∃ B₁ B₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      B₁ '' sphere (0 : E3) 1 = E ∪
        Q.symm '' (liftPlaneDiffeomorph hv b u hu.ne' A '' boundedCylinderNorthernCap v) ∧
      B₂ '' sphere (0 : E3) 1 = M ∪
        Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' B '' boundedCylinderNorthernCap v) ∧
      B₁ '' closedBall (0 : E3) 1 ⊆ B₂ '' ball (0 : E3) 1 := by
  obtain ⟨B₁, hB₁⟩ := exists_curved_closing_ball_of_lower_cap_normalization hv A hab hs hu
    N₁ Q hQ hN₁ hE
  obtain ⟨B₂, hB₂⟩ := exists_curved_closing_ball_of_lower_cap_normalization hv B hdb ht hw
    N₂ Q hQ hN₂ hM
  refine ⟨B₁, B₂, hB₁, hB₂, ?_⟩
  have hQinv (y : E3) : inner Real v (Q.symm y) = inner Real v y := by
    rw [← hQ (Q.symm y), Q.apply_symm_apply]
  have hupper (C : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
      (r : Real) (hr : 0 < r) :
      ∀ y ∈ Q.symm '' (liftPlaneDiffeomorph hv b r hr.ne' C '' boundedCylinderNorthernCap v),
        b ≤ inner Real v y := by
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    rw [hQinv, inner_liftPlaneDiffeomorph]
    exact le_add_of_nonneg_right (mul_nonneg hr.le
      (height_nonneg_of_mem_boundedCylinderNorthernCap hx))
  have hdis : Disjoint
      (Q.symm '' (liftPlaneDiffeomorph hv b u hu.ne' A '' boundedCylinderNorthernCap v))
      (Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' B '' boundedCylinderNorthernCap v)) := by
    exact (disjoint_image_iff Q.symm.injective).mpr
      (disjoint_curved_closing_caps_of_nested_fillings hv b u w hu hw A B hAB hscale)
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] EuclideanSpace Real (Fin 2) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro hv0; simp [hv0] at hv)).repr
  let : Nontrivial (Hemisphere.Plane v) := Module.nontrivial_of_finrank_pos
    (R := Real) (by rw [J.toLinearEquiv.finrank_eq]; norm_num)
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := Hemisphere.Plane v) (x := 0)).mpr
    (show (0 : Real) ≤ 1 by norm_num)
  let p : E3 := (b + u * (1 / 2)) • v + (A x : E3)
  have hpheight : inner Real v p = b + u * (1 / 2) := inner_heightCoordinates hv (_, A x)
  have hpcap : p ∈ liftPlaneDiffeomorph hv b u hu.ne' A '' boundedCylinderNorthernCap v := by
    have hslice := lifted_cap_slice_eq_circle hv b u hu.ne' A
      (show (1 / 2 : Real) ∈ Ico 0 1 by constructor <;> norm_num)
    have hp : p ∈ (fun q : Hemisphere.Plane v => (b + u * (1 / 2)) • v + (A q : E3)) ''
        sphere (0 : Hemisphere.Plane v) 1 := ⟨x, hx, rfl⟩
    rw [← hslice] at hp
    exact hp.1
  have hnormalized : (B₂.trans N₂) '' sphere (0 : E3) 1 =
      (liftPlaneDiffeomorph hv d t ht.ne B '' boundedCylinderNorthernCap v) ∪
      ((fun z : Real × Hemisphere.Plane v => z.1 • v + (B z.2 : E3)) ''
        (Icc d b ×ˢ sphere (0 : Hemisphere.Plane v) 1)) ∪
      (liftPlaneDiffeomorph hv b w hw.ne' B '' boundedCylinderNorthernCap v) := by
    change (N₂ ∘ B₂) '' sphere (0 : E3) 1 = _
    rw [image_comp, hB₂, image_union, hM, cylinder_circle_image, image_image]
    congr 1
    have heq : EqOn (N₂ ∘ Q.symm) id
        (liftPlaneDiffeomorph hv b w hw.ne' B '' boundedCylinderNorthernCap v) := by
      intro z hz
      change N₂ (Q.symm z) = z
      rw [hN₂ (hupper B w hw _ (mem_image_of_mem Q.symm hz)), Q.apply_symm_apply]
    simpa only [Function.comp_def, image_id] using image_congr heq
  have hpinside : p ∈ (B₂.trans N₂) '' ball (0 : E3) 1 := by
    apply mem_capped_cylinder_ball_of_upper_collar hv hdb (neg_pos.mpr ht) hw B
      (B₂.trans N₂).toHomeomorph
    · convert hnormalized using 1
      · rfl
      · simp only [neg_neg]
    · rw [hpheight]
      constructor <;> linarith
    · have hproj : (Hemisphere.Plane v).orthogonalProjectionOnto p = A x :=
        congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply (_, A x))
      rw [hproj]
      exact hAB (mem_image_of_mem A (sphere_subset_closedBall hx))
  have hpB₂ : Q.symm p ∈ B₂ '' ball (0 : E3) 1 := by
    obtain ⟨z, hz, heq⟩ := hpinside
    refine ⟨z, hz, N₂.injective ?_⟩
    change N₂ (B₂ z) = N₂ (Q.symm p)
    rw [hN₂ (x := Q.symm p) (by change b ≤ inner Real v (Q.symm p); rw [hQinv, hpheight]; linarith),
      Q.apply_symm_apply]
    exact heq
  exact closing_ball_subset_of_one_interior_point B₁ B₂ hB₁ hB₂ hEM hdis hEheight hMheight
    (hupper A u hu) (hupper B w hw)
    (fun y hy hh => closing_cap_rim_subset hv A hab hs hu N₁ Q hQ hN₁ hE hy hh)
    (fun y hy hh => closing_cap_rim_subset hv B hdb ht hw N₂ Q hQ hN₂ hM hy hh)
    (mem_image_of_mem Q.symm hpcap) hpB₂

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
