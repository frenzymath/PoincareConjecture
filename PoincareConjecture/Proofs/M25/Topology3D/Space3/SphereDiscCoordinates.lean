import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ComplementaryStereographic

set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] space3_stereographic_dimension

theorem sphereStereo_image_closedBall (v : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    (stereographic' 2 v).symm '' closedBall 0 r =
      {q : UnitTwoSphere | stereographicCapHeight r ≤ ⟪-(v : E3), (q : E3)⟫_ℝ} := by
  let U : (ℝ ∙ (v : E3))ᗮ ≃ₗᵢ[ℝ] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr
  have hc : (fun x : E2 => ((stereographic' 2 v).symm x : E3)) =
      (fun w => (stereoInvFun (norm_eq_of_mem_sphere v) w : E3)) ∘ U.symm := rfl
  have himage : (fun x : E2 => ((stereographic' 2 v).symm x : E3)) '' closedBall 0 r =
      {y : E3 | ‖y‖ = 1 ∧ stereographicCapHeight r ≤ ⟪-(v : E3), y⟫_ℝ} := by
    rw [hc, image_comp, U.symm.image_closedBall, map_zero]
    exact stereoInvFun_image_closedBall_pos (v : E3) (norm_eq_of_mem_sphere v) hr
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hm : ((stereographic' 2 v).symm x : E3) ∈
        (fun x : E2 => ((stereographic' 2 v).symm x : E3)) '' closedBall 0 r :=
      ⟨x, hx, rfl⟩
    rw [himage] at hm
    exact hm.2
  · intro hq
    have hm : (q : E3) ∈
        (fun x : E2 => ((stereographic' 2 v).symm x : E3)) '' closedBall 0 r := by
      rw [himage]
      exact ⟨norm_eq_of_mem_sphere q, hq⟩
    obtain ⟨x, hx, heq⟩ := hm
    exact ⟨x, hx, Subtype.ext heq⟩

theorem sphereStereo_image_sphere (v : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    (stereographic' 2 v).symm '' sphere 0 r =
      {q : UnitTwoSphere | stereographicCapHeight r = ⟪-(v : E3), (q : E3)⟫_ℝ} := by
  let U : (ℝ ∙ (v : E3))ᗮ ≃ₗᵢ[ℝ] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr
  have hc : (fun x : E2 => ((stereographic' 2 v).symm x : E3)) =
      (fun w => (stereoInvFun (norm_eq_of_mem_sphere v) w : E3)) ∘ U.symm := rfl
  have himage : (fun x : E2 => ((stereographic' 2 v).symm x : E3)) '' sphere 0 r =
      {y : E3 | ‖y‖ = 1 ∧ stereographicCapHeight r = ⟪-(v : E3), y⟫_ℝ} := by
    rw [hc, image_comp, U.symm.image_sphere, map_zero]
    exact stereoInvFun_image_sphere_pos (v : E3) (norm_eq_of_mem_sphere v) hr
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hm : ((stereographic' 2 v).symm x : E3) ∈
        (fun x : E2 => ((stereographic' 2 v).symm x : E3)) '' sphere 0 r :=
      ⟨x, hx, rfl⟩
    rw [himage] at hm
    exact hm.2
  · intro hq
    have hm : (q : E3) ∈
        (fun x : E2 => ((stereographic' 2 v).symm x : E3)) '' sphere 0 r := by
      rw [himage]
      exact ⟨norm_eq_of_mem_sphere q, hq⟩
    obtain ⟨x, hx, heq⟩ := hm
    exact ⟨x, hx, Subtype.ext heq⟩

theorem sphereStereo_complementary_discs (v : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    ((stereographic' 2 v).symm '' closedBall 0 r) ∪
        ((stereographic' 2 (-v)).symm '' closedBall 0 (4 / r)) = univ ∧
    ((stereographic' 2 v).symm '' closedBall 0 r) ∩
        ((stereographic' 2 (-v)).symm '' closedBall 0 (4 / r)) =
          (stereographic' 2 v).symm '' sphere 0 r ∧
    (stereographic' 2 (-v)).symm '' sphere 0 (4 / r) =
      (stereographic' 2 v).symm '' sphere 0 r := by
  have hR : 0 < 4 / r := div_pos (by norm_num) hr
  rw [sphereStereo_image_closedBall v hr, sphereStereo_image_closedBall (-v) hR,
    sphereStereo_image_sphere v hr, sphereStereo_image_sphere (-v) hR,
    stereographicCapHeight_complement hr]
  simp only [coe_neg_sphere, neg_neg, inner_neg_left]
  constructor
  · ext q
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    rcases le_total (stereographicCapHeight r) (-⟪(v : E3), (q : E3)⟫_ℝ) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · constructor <;> ext q
    · simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h₁, h₂⟩
        linarith
      · intro h
        constructor <;> linarith
    · simp only [mem_ofPred_eq]
      constructor <;> intro h <;> linarith

end PoincareConjecture.M25.Topology3D
