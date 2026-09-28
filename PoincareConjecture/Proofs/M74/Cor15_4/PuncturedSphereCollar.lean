import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereChart

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

noncomputable def punctureCollar (p : RoundCylinderSpace) : StandardCapSpace :=
  B.punctureChart d (B.map ((1 + p.2) • p.1.1))

private theorem radial_norm (q : UnitTwoSphere) {s : ℝ} (hs : -1 < s) :
    ‖(1 + s) • q.1‖ = 1 + s := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
    mem_sphere_zero_iff_norm.mp q.2, mul_one]

private theorem radial_mem_ball {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) : (1 + p.2) • p.1.1 ∈ ball 0 2 := by
  rw [mem_ball_zero_iff, radial_norm p.1 hp.2.1]
  linarith [hp.2.2]

private theorem radial_ne_zero {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) : (1 + p.2) • p.1.1 ≠ 0 := by
  apply norm_pos_iff.mp
  rw [radial_norm p.1 hp.2.1]
  linarith [hp.2.1]

theorem punctureCollar_contMDiffOn :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (B.punctureCollar d)
      (univ ×ˢ Ioo (-1) 1) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  have hr : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun p : RoundCylinderSpace => (1 + p.2) • p.1.1) :=
    (contMDiff_const.add contMDiff_snd).smul
      ((contMDiff_coe_sphere (E := StandardCapSpace) (n := 2)).comp contMDiff_fst)
  apply (B.punctureChart_contMDiffOn d).comp
    (B.map_smooth.comp hr.contMDiffOn (fun _ hp => radial_mem_ball hp))
  intro p hp
  exact (B.map_mem_punctureChart_source_iff d (radial_mem_ball hp)).mpr
    (radial_ne_zero hp)

theorem punctureCollar_injOn :
    InjOn (B.punctureCollar d) (univ ×ˢ Ioo (-1) 1) := by
  intro p hp q hq hpq
  have hmap := (B.punctureChart d).injOn
    ((B.map_mem_punctureChart_source_iff d (radial_mem_ball hp)).mpr (radial_ne_zero hp))
    ((B.map_mem_punctureChart_source_iff d (radial_mem_ball hq)).mpr (radial_ne_zero hq)) hpq
  have hr := B.left_inverse.injOn (radial_mem_ball hp) (radial_mem_ball hq) hmap
  have hn := congrArg norm hr
  rw [radial_norm p.1 hp.2.1, radial_norm q.1 hq.2.1] at hn
  have hs : p.2 = q.2 := by linarith
  apply Prod.ext _ hs
  apply Subtype.ext
  rw [hs] at hr
  exact (smul_right_injective _ (by linarith [hq.2.1] : (1 : ℝ) + q.2 ≠ 0)) hr

theorem punctureCollar_negative_image :
    B.punctureCollar d '' (univ ×ˢ Ioo (-1) 0) =
      B.punctureChart d '' ((B.map '' ball (0 : StandardCapSpace) 1) \ {B.map 0}) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp1 : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩
    refine ⟨B.map ((1 + p.2) • p.1.1), ⟨⟨_, ?_, rfl⟩, ?_⟩, rfl⟩
    · rw [mem_ball_zero_iff, radial_norm p.1 hp.2.1]
      linarith [hp.2.2]
    · have hs := (B.map_mem_punctureChart_source_iff d (radial_mem_ball hp1)).mpr
        (radial_ne_zero hp1)
      simpa only [B.punctureChart_source d, mem_compl_iff] using hs
  · rintro ⟨a, ⟨⟨x, hx, rfl⟩, hx0⟩, rfl⟩
    have hxne : x ≠ 0 := by
      intro h
      apply hx0
      simp [h]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    let q : UnitTwoSphere := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)]⟩
    refine ⟨(q, ‖x‖ - 1), ⟨mem_univ _, ?_, ?_⟩, ?_⟩
    · linarith
    · have := mem_ball_zero_iff.mp hx
      linarith
    · change B.punctureChart d (B.map ((1 + (‖x‖ - 1)) • (‖x‖⁻¹ • x))) = _
      rw [show 1 + (‖x‖ - 1) = ‖x‖ by ring, smul_smul,
        mul_inv_cancel₀ (ne_of_gt hn), one_smul]

theorem punctureCollar_negative_unbounded :
    ¬Bornology.IsBounded (B.punctureCollar d '' (univ ×ˢ Ioo (-1) 0)) := by
  rw [B.punctureCollar_negative_image d]
  exact B.punctureChart_image_puncturedBall_unbounded d (by norm_num) (by norm_num)

theorem punctureCollar_side_eq_neg_one (side : ℝ) (hside : side * side = 1)
    {U : Set StandardCapSpace} (hU : Bornology.IsBounded U)
    (hcontain : (fun p : RoundCylinderSpace => B.punctureCollar d (p.1, side * p.2)) ''
      (univ ×ˢ Ioo (-1) 0) ⊆ U) : side = -1 := by
  have hcases : side = 1 ∨ side = -1 := by
    have hfactor : (side - 1) * (side + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · left; linarith
    · right; linarith
  rcases hcases with rfl | h
  · exfalso
    apply B.punctureCollar_negative_unbounded d
    apply hU.subset
    simpa only [one_mul, Prod.eta] using hcontain
  · exact h

end PoincareConjecture.SurgeryBallEmbedding
