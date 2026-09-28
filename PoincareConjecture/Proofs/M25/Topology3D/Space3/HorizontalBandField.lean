import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockTracks












set_option autoImplicit false

open Set Function
open scoped ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D


noncomputable def horizontalBandProjection (u : UnitTwoSphere) : E3 →L[ℝ] E2 :=
  (ContinuousLinearMap.fst ℝ E2 ℝ).comp (heightPlaneCoordinates u).toContinuousLinearMap


@[simp] theorem horizontalBandProjection_apply (u : UnitTwoSphere) (y : E3) :
    horizontalBandProjection u y = (heightPlaneCoordinates u y).1 := rfl


noncomputable def horizontalBandLift (u : UnitTwoSphere) : (ℝ × E2) ≃L[ℝ] E3 :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans (heightPlaneCoordinates u).symm


@[simp] theorem horizontalBandLift_apply (u : UnitTwoSphere) (p : ℝ × E2) :
    horizontalBandLift u p = (heightPlaneCoordinates u).symm (p.2, p.1) := rfl


@[simp] theorem horizontalBandProjection_lift (u : UnitTwoSphere) (z : ℝ) (p : E2) :
    horizontalBandProjection u (horizontalBandLift u (z, p)) = p := by
  change (heightPlaneCoordinates u ((heightPlaneCoordinates u).symm (p, z))).1 = p
  rw [ContinuousLinearEquiv.apply_symm_apply]


@[simp] theorem horizontalBandLift_height (u : UnitTwoSphere) (z : ℝ) (p : E2) :
    ⟪(u : E3), horizontalBandLift u (z, p)⟫_ℝ = z := by
  rw [← heightPlaneCoordinates_snd u]
  change (heightPlaneCoordinates u ((heightPlaneCoordinates u).symm (p, z))).2 = z
  rw [ContinuousLinearEquiv.apply_symm_apply]


theorem horizontalBandLift_reconstruct (u : UnitTwoSphere) (y : E3) (z : ℝ)
    (hy : ⟪(u : E3), y⟫_ℝ = z) :
    horizontalBandLift u (z, horizontalBandProjection u y) = y :=
  heightPlaneCoordinates_reconstruct u y z hy


noncomputable def horizontalBandField (u : UnitTwoSphere) (F : E3 → E3)
    (p : ℝ × E2) : E2 :=
  horizontalBandProjection u (F (horizontalBandLift u p))


theorem horizontalBandField_contDiff (u : UnitTwoSphere) (F : E3 → E3)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (horizontalBandField u F) :=
  (horizontalBandProjection u).contDiff.comp (hF.comp (horizontalBandLift u).contDiff)


theorem horizontalBandField_tsupport (u : UnitTwoSphere) (F : E3 → E3) :
    tsupport (horizontalBandField u F) ⊆ (horizontalBandLift u) ⁻¹' tsupport F := by
  apply closure_minimal _ ((isClosed_tsupport F).preimage (horizontalBandLift u).continuous)
  intro p hp
  apply subset_tsupport
  intro hzero
  exact hp (by simp only [horizontalBandField, hzero, map_zero])



theorem horizontalBandField_hasCompactSupport (u : UnitTwoSphere) (F : E3 → E3)
    (hF : HasCompactSupport F) : HasCompactSupport (horizontalBandField u F) := by
  exact (hF.comp_homeomorph (horizontalBandLift u).toHomeomorph).comp_left
    (horizontalBandProjection u).map_zero


theorem horizontalBandField_clock_bounds (u : UnitTwoSphere) (F : E3 → E3)
    (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ∃ K L : ℝ≥0, LipschitzWith K (clockField (horizontalBandField u F)) ∧
      ∀ p, ‖clockField (horizontalBandField u F) p‖ ≤ L :=
  clockField_bounds (horizontalBandField u F) (horizontalBandField_contDiff u F hF)
    (horizontalBandField_hasCompactSupport u F hs)


theorem horizontalBandField_evolution_hasCompactSupport (u : UnitTwoSphere)
    (F : E3 → E3) (hs : HasCompactSupport F) {K L : ℝ≥0}
    (hK : LipschitzWith K (clockField (horizontalBandField u F)))
    (hL : ∀ p, ‖clockField (horizontalBandField u F) p‖ ≤ L) (s t : ℝ) :
    HasCompactSupport (fun p => clockEvolution (horizontalBandField u F) hK hL s t p - p) :=
  clockEvolution_hasCompactSupport (horizontalBandField u F) hK hL
    (horizontalBandField_hasCompactSupport u F hs) s t

end PoincareConjecture.M25.Topology3D
