import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.PointAdjustment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Puncture










noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


def puncturedDiffeomorph (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hF : F 0 = 0) : Diffeomorph (𝓡 3) (𝓡 3)
      puncturedThreeSpace puncturedThreeSpace ∞ := by
  have hi : F.symm 0 = 0 := by
    simpa only [hF] using F.symm_apply_apply 0
  let e : puncturedThreeSpace ≃ puncturedThreeSpace :=
    { toFun := fun x => ⟨F x, fun hx => x.property (F.injective (hx.trans hF.symm))⟩
      invFun := fun x => ⟨F.symm x, fun hx => x.property (F.symm.injective (hx.trans hi.symm))⟩
      left_inv := fun x => Subtype.ext (F.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (F.apply_symm_apply x) }
  refine ⟨e, ?_, ?_⟩
  · apply (ContMDiff.subtypeVal_comp_iff puncturedThreeSpace e).mp
    exact F.contMDiff.comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff puncturedThreeSpace e.symm).mp
    exact F.symm.contMDiff.comp contMDiff_subtype_val

@[simp] theorem puncturedDiffeomorph_apply
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (hF : F 0 = 0)
    (x : puncturedThreeSpace) : (puncturedDiffeomorph F hF x : E3) = F x := rfl



theorem exists_ambient_sphere_map_fixing_puncture
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hinside : (0 : E3) ∈ F '' ball 0 1) :
    ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      G 0 = 0 ∧ ∀ q ∈ sphere (0 : E3) 1, G q = F q := by
  have ha : ‖F.symm 0‖ < 1 := by
    obtain ⟨x, hx, heq⟩ := hinside
    rw [← heq, F.symm_apply_apply]
    simpa [mem_ball, dist_zero_right] using hx
  obtain ⟨r, D, -, hr, hD, hfix⟩ := exists_diffeomorph_move_zero_in_unitBall ha
  refine ⟨D.trans F, ?_, ?_⟩
  · change F (D 0) = 0
    rw [hD, F.apply_symm_apply]
  · intro q hq
    have hqnorm : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp hq
    change F (D q) = F q
    rw [hfix q (by simpa only [hqnorm] using hr.le)]




theorem exists_cylinder_coordinates_of_ambient_sphere
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (A B : Set E3) (hA : IsPreconnected A) (hB : IsPreconnected B)
    (havoid : (0 : E3) ∉ F '' sphere 0 1)
    (hcover : A ∪ B = {0}ᶜ \ (F '' sphere 0 1))
    (hescape : ∀ L : Set E3, IsCompact L → L ⊆ {0}ᶜ →
      ¬ A ⊆ L ∧ ¬ B ⊆ L) :
    ∃ G : Diffeomorph CylModel (𝓡 3) (S2 × ℝ) puncturedThreeSpace ∞,
      ∀ q : S2, (G (q, 0) : E3) = F q := by
  let K := F '' closedBall (0 : E3) 1
  have hK : IsCompact K := (isCompact_closedBall 0 1).image F.continuous
  have hint : interior K = F '' ball 0 1 := by
    change interior (F.toHomeomorph '' closedBall (0 : E3) 1) = _
    rw [← F.toHomeomorph.image_interior, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    rfl
  have hfront : frontier K = F '' sphere 0 1 := by
    change frontier (F.toHomeomorph '' closedBall (0 : E3) 1) = _
    rw [← F.toHomeomorph.image_frontier, frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    rfl
  have hnonempty : (interior K).Nonempty := by
    rw [hint]
    exact ⟨F 0, mem_image_of_mem F (mem_ball_self zero_lt_one)⟩
  have hinside : (0 : E3) ∈ F '' ball 0 1 := by
    rw [← hint]
    apply Topology.puncture_mem_interior_of_escaping_sides hK hnonempty
      (by simpa [hfront] using havoid) hA hB
      (by simpa [hfront] using hcover) hescape
  obtain ⟨G, hG0, hGsphere⟩ := exists_ambient_sphere_map_fixing_puncture F hinside
  refine ⟨sphereCylinderDiffeomorphPunctured.trans (puncturedDiffeomorph G hG0), ?_⟩
  intro q
  change G (sphereCylinderDiffeomorphPunctured (q, 0) : E3) = F q
  rw [sphereCylinderDiffeomorphPunctured_zero]
  exact hGsphere q q.property

end Poincare
