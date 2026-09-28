import PoincareConjecture.Proofs.M74.Cor15_4.CollarReparametrization
import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereImmersion
import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereStandardEnd










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

open M74 M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)



noncomputable def shiftedPunctureCollar : RoundCylinderSpace → StandardCapSpace :=
  B.punctureCollar d ∘ shiftCollar



theorem shiftedPunctureCollar_isCollarEmbedding :
    IsCollarEmbedding (B.shiftedPunctureCollar d) :=
  isCollarEmbedding_comp_shift (B.punctureCollar_isCollarEmbedding d)

private theorem shifted_radial_norm {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
    ‖(1 + shiftCollarParam p.2) • p.1.1‖ = 1 + shiftCollarParam p.2 := by
  have hs := shiftCollarParam_mem hp.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hs.1]),
    mem_sphere_zero_iff_norm.mp p.1.2, mul_one]



theorem shiftedPunctureCollar_negative_image :
    B.shiftedPunctureCollar d '' (univ ×ˢ Ioo (-1) 0) =
      B.punctureChart d '' ((B.map '' ball (0 : StandardCapSpace) (3 / 2)) \ {B.map 0}) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp1 : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩
    have hs := shiftCollarParam_mem hp1.2
    have hh : shiftCollarParam p.2 < 1 / 2 :=
      (div_lt_iff₀ (by linarith [hp.2.1] : 0 < 2 + p.2)).mpr (by linarith [hp.2.2])
    have hxball : (1 + shiftCollarParam p.2) • p.1.1 ∈ ball (0 : StandardCapSpace) (3 / 2) := by
      rw [mem_ball_zero_iff, shifted_radial_norm hp1]
      linarith
    have hx2 := ball_subset_ball (by norm_num : (3 / 2 : ℝ) ≤ 2) hxball
    have hxne : (1 + shiftCollarParam p.2) • p.1.1 ≠ 0 := by
      apply norm_pos_iff.mp
      rw [shifted_radial_norm hp1]
      linarith [hs.1]
    refine ⟨B.map ((1 + shiftCollarParam p.2) • p.1.1), ⟨⟨_, hxball, rfl⟩, ?_⟩, rfl⟩
    have hsource := (B.map_mem_punctureChart_source_iff d hx2).mpr hxne
    simpa only [B.punctureChart_source d, mem_compl_iff] using hsource
  · rintro ⟨a, ⟨⟨x, hx, rfl⟩, hx0⟩, rfl⟩
    have hxne : x ≠ 0 := by
      intro h
      apply hx0
      simp [h]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hnlt : ‖x‖ < 3 / 2 := mem_ball_zero_iff.mp hx
    let q : UnitTwoSphere := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)]⟩
    have ht : ‖x‖ - 1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hu := unshiftCollarParam_mem ht
    have huneg : unshiftCollarParam (‖x‖ - 1) < 0 :=
      (div_lt_iff₀ (by linarith : 0 < 2 - (‖x‖ - 1))).mpr (by linarith)
    refine ⟨(q, unshiftCollarParam (‖x‖ - 1)), ⟨mem_univ _, hu.1, huneg⟩, ?_⟩
    change B.punctureChart d
      (B.map ((1 + shiftCollarParam (unshiftCollarParam (‖x‖ - 1))) • (‖x‖⁻¹ • x))) = _
    rw [shift_unshiftCollarParam ht, show 1 + (‖x‖ - 1) = ‖x‖ by ring,
      smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]



theorem shiftedPunctureCollar_negative_unbounded :
    ¬Bornology.IsBounded (B.shiftedPunctureCollar d '' (univ ×ˢ Ioo (-1) 0)) := by
  rw [B.shiftedPunctureCollar_negative_image d]
  exact B.punctureChart_image_puncturedBall_unbounded d (by norm_num) (by norm_num)



theorem shiftedSchoenflies_side_eq_neg_one {δ : ℝ}
    (D : SchoenfliesData (B.shiftedPunctureCollar d) δ) : D.side = -1 := by
  have hcases : D.side = 1 ∨ D.side = -1 := by
    have hfactor : (D.side - 1) * (D.side + 1) = 0 := by nlinarith [D.side_sq]
    rcases mul_eq_zero.mp hfactor with h | h
    · left; linarith
    · right; linarith
  rcases hcases with h | h
  · exfalso
    apply B.shiftedPunctureCollar_negative_unbounded d
    apply D.inside_bounded.subset
    simpa only [h, one_mul, Prod.eta] using D.collar_inside
  · exact h



theorem shiftedSchoenflies_original_boundary
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) (q : UnitTwoSphere) :
    D.chart (D.radial (1 / 2) • (D.boundary_map q).1) = B.punctureCollar d (q, 0) := by
  have h := D.chart_collar q (1 / 2) (by norm_num)
  rw [B.shiftedSchoenflies_side_eq_neg_one d D] at h
  norm_num [shiftedPunctureCollar, shiftCollar, shiftCollarParam, Function.comp_apply] at h
  exact h




theorem exists_shiftedSchoenflies_boundary (hS : SchoenfliesService) :
    ∃ D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4),
      D.side = -1 ∧ 0 < D.radial (1 / 2) ∧ D.radial (1 / 2) < D.radius ∧
      ∀ q : UnitTwoSphere, D.chart (D.radial (1 / 2) • (D.boundary_map q).1) =
        B.punctureCollar d (q, 0) := by
  obtain ⟨D⟩ := hS (B.shiftedPunctureCollar d) (B.shiftedPunctureCollar_isCollarEmbedding d)
    (1 / 4) (by norm_num) (by norm_num)
  exact ⟨D, B.shiftedSchoenflies_side_eq_neg_one d D, D.radial_pos _ (by norm_num),
    D.radial_lt _ (by norm_num), B.shiftedSchoenflies_original_boundary d D⟩



theorem exists_schoenflies_inside_exterior (hS : SchoenfliesService) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ D : SchoenfliesData (B.punctureCollar d) δ,
      D.side = -1 ∧ D.inside = (B.punctureChart d) '' B.closedBallᶜ := by
  obtain ⟨D⟩ := hS (B.punctureCollar d) (B.punctureCollar_isCollarEmbedding d) δ hδ hδ1
  exact ⟨D, B.schoenflies_side_eq_neg_one d D, B.schoenflies_inside_eq_exterior d D⟩

end PoincareConjecture.SurgeryBallEmbedding
