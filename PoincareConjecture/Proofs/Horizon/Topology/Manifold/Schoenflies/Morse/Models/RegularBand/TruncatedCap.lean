import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.TruncatedCap.Clock
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.TruncatedCap.HeightAction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_ambient_truncated_cap_normalization
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {a : Real} (ha : 0 < a) (ha1 : a < 1) :
    ∃ φ : Real ≃ₘ[Real] Real, StrictMono φ ∧
      (∀ t, t ≤ (1+a)/2 → φ t = t-a) ∧
      (∀ t, 1 ≤ t → φ t = t) ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y : E3, F y = (c+s*a+s*φ ((inner Real v y-c)/s)) • v +
          ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3)) ∧
        (∀ y : E3, (Hemisphere.Plane v).orthogonalProjectionOnto (F y) =
          (Hemisphere.Plane v).orthogonalProjectionOnto y) ∧
        (∀ y : E3, (inner Real v y-c)/s ≤ (1+a)/2 → F y = y) ∧
        (∀ y : E3, 1 ≤ (inner Real v y-c)/s → F y = y+(s*a) • v) ∧
        F '' ((liftPlaneDiffeomorph hv c s hs A '' boundedCylinderNorthernCap v) ∩
          {y : E3 | a ≤ (inner Real v y-c)/s}) =
            liftPlaneDiffeomorph hv (c+s*a) s hs A '' boundedCylinderNorthernCap v := by
  obtain ⟨φ, hmono, hlow, hhigh⟩ := TruncatedCap.exists_clock ha ha1
  have hzero : φ a = 0 := by rw [hlow a (by linarith)]; ring
  let G := TruncatedCap.heightAction hv φ
  let L := liftPlaneDiffeomorph hv c s hs A
  let L' := liftPlaneDiffeomorph hv (c+s*a) s hs A
  let F := (L.symm.trans G).trans L'
  have hFL (z : E3) : F (L z) = L' (G z) := by
    change L' (G (L.symm (L z))) = _
    rw [L.symm_apply_apply]
  have hnorm (z : E3) : (inner Real v (L z)-c)/s = inner Real v z := by
    change (inner Real v (liftPlaneDiffeomorph hv c s hs A z)-c)/s = _
    rw [inner_liftPlaneDiffeomorph, add_sub_cancel_left, mul_div_cancel_left₀ _ hs]
  have hpoint (y : E3) : F y = (c+s*a+s*φ ((inner Real v y-c)/s)) • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) := by
    obtain ⟨z, rfl⟩ := L.surjective y
    change F (L z) = (c+s*a+s*φ ((inner Real v (L z)-c)/s)) • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto (L z) : E3)
    rw [hFL, hnorm]
    change liftPlaneDiffeomorph hv (c+s*a) s hs A (TruncatedCap.heightAction hv φ z) = _
    rw [liftPlaneDiffeomorph_apply, TruncatedCap.heightAction_height,
      TruncatedCap.heightAction_projection]
    rw [show (Hemisphere.Plane v).orthogonalProjectionOnto (L z) =
      A ((Hemisphere.Plane v).orthogonalProjectionOnto z) from
        projection_liftPlaneDiffeomorph hv c s hs A z]
  refine ⟨φ, hmono, hlow, hhigh, F, hpoint, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [hpoint]
    simp [Hemisphere.Plane,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
  · intro y hy
    rw [hpoint, hlow _ hy]
    have hh : c+s*a+s*((inner Real v y-c)/s-a) = inner Real v y := by
      field_simp
      ring
    rw [hh]
    exact (heightCoordinates hv).apply_symm_apply y
  · intro y hy
    rw [hpoint, hhigh _ hy]
    have hh : c+s*a+s*((inner Real v y-c)/s) = inner Real v y+s*a := by
      field_simp
      ring
    rw [hh, add_smul]
    have hsplit : inner Real v y • v +
        ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y :=
      (heightCoordinates hv).apply_symm_apply y
    calc
      _ = (inner Real v y • v +
          ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3)) + (s*a) • v := by abel
      _ = y + (s*a) • v := by rw [hsplit]
  · have hsource : (L '' boundedCylinderNorthernCap v) ∩
        {y : E3 | a ≤ (inner Real v y-c)/s} =
        L '' (boundedCylinderNorthernCap v ∩ {z : E3 | a ≤ inner Real v z}) := by
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, ht⟩
        have ht' : a ≤ (inner Real v (L z)-c)/s := ht
        rw [hnorm] at ht'
        exact ⟨z, ⟨hz, ht'⟩, rfl⟩
      · rintro ⟨z, ⟨hz, ht⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, by change a ≤ (inner Real v (L z)-c)/s; rw [hnorm]; exact ht⟩
    change F '' ((L '' boundedCylinderNorthernCap v) ∩ _) = L' '' boundedCylinderNorthernCap v
    rw [hsource, ← image_comp, show F ∘ L = L' ∘ G from funext hFL, image_comp]
    rw [TruncatedCap.image_heightAction_truncated_cap hv ha ha1 φ hmono hzero hhigh]

end Poincare.Manifold.Schoenflies
