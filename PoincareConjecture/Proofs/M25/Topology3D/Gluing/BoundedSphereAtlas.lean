import PoincareConjecture.Proofs.M25.Mathlib.StereographicAntipode
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SphereGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_bounded_threeSphere_stereographic_atlas
    (v : UnitThreeSphere) {rPlus rMinus : ℝ}
    (hPlus : 0 < rPlus) (hMinus : 0 < rMinus)
    (hproduct : 4 < rPlus * rMinus) :
    ∃ (B : E3 ≃ₗᵢ[ℝ] E3)
      (c0 c1 : OpenPartialHomeomorph UnitThreeSphere E3),
      (∀ x : E3, x ≠ 0 →
        threeSphereStereographic (-v) ((threeSphereStereographic v).symm x) =
          (4 / ‖x‖ ^ 2) • B x) ∧
      (c0 : UnitThreeSphere → E3) = threeSphereStereographic v ∧
      (c1 : UnitThreeSphere → E3) = threeSphereStereographic (-v) ∧
      (c0.symm : E3 → UnitThreeSphere) = (threeSphereStereographic v).symm ∧
      (c1.symm : E3 → UnitThreeSphere) = (threeSphereStereographic (-v)).symm ∧
      c0.source = (threeSphereStereographic v).source ∩
        (threeSphereStereographic v) ⁻¹' ball 0 rPlus ∧
      c1.source = (threeSphereStereographic (-v)).source ∩
        (threeSphereStereographic (-v)) ⁻¹' ball 0 rMinus ∧
      c0.target = ball 0 rPlus ∧ c1.target = ball 0 rMinus ∧
      c0.source ∪ c1.source = univ ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ c0 c0.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ c1 c1.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ c0.symm c0.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ c1.symm c1.target ∧
      (c0.symm.trans c1).source =
        {x : E3 | 4 / rMinus < ‖x‖ ∧ ‖x‖ < rPlus} ∧
      (∀ x ∈ (c0.symm.trans c1).source,
        c1 (c0.symm x) = (4 / ‖x‖ ^ 2) • B x) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  obtain ⟨B, hB⟩ := exists_stereographic_antipode_linearIsometry (n := 3) v
  change ∀ x : E3, x ≠ 0 →
    threeSphereStereographic (-v) ((threeSphereStereographic v).symm x) =
      (4 / ‖x‖ ^ 2) • B x at hB
  let s0 := threeSphereStereographic v
  let s1 := threeSphereStereographic (-v)
  let c0 := (s0.symm.restrOpen (ball 0 rPlus) isOpen_ball).symm
  let c1 := (s1.symm.restrOpen (ball 0 rMinus) isOpen_ball).symm
  have ht0 : c0.target = ball 0 rPlus := by
    change s0.target ∩ ball 0 rPlus = ball 0 rPlus
    simp [s0]
  have ht1 : c1.target = ball 0 rMinus := by
    change s1.target ∩ ball 0 rMinus = ball 0 rMinus
    simp [s1]
  have hvalid (x : E3) : s0.symm x ∈ s1.source ↔ x ≠ 0 := by
    have h := threeSphereStereographic_transition_source v
    have hh : x ∈ (s0.symm.trans s1).source ↔ x ≠ 0 := by
      rw [h]
      simp
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      s0, threeSphereStereographic_target, mem_inter_iff, mem_univ, true_and,
      mem_preimage] using hh
  have hnorm (x : E3) (hx : x ≠ 0) : ‖s1 (s0.symm x)‖ = 4 / ‖x‖ := by
    rw [hB x hx, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _)), B.norm_map]
    field_simp [norm_ne_zero_iff.mpr hx]
  have hcover : c0.source ∪ c1.source = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p = v
    · right
      change p ∈ s1.source ∩ s1 ⁻¹' ball 0 rMinus
      subst p
      have hz : s1 v = 0 := by
        simpa only [neg_neg] using threeSphereStereographic_apply_antipode (-v)
      refine ⟨?_, ?_⟩
      · simpa only [s1, threeSphereStereographic_source, mem_compl_iff,
          mem_singleton_iff] using ne_neg_of_mem_unit_sphere ℝ v
      · simpa only [mem_preimage, hz, mem_ball, dist_self] using hMinus
    · have hp0 : p ∈ s0.source := by
        simpa only [s0, threeSphereStereographic_source, mem_compl_iff,
          mem_singleton_iff] using hp
      by_cases hlt : ‖s0 p‖ < rPlus
      · left
        exact ⟨hp0, by simpa only [OpenPartialHomeomorph.symm_symm,
          mem_preimage, mem_ball_zero_iff] using hlt⟩
      · right
        have hr : 0 < ‖s0 p‖ := hPlus.trans_le (le_of_not_gt hlt)
        have hx : s0 p ≠ 0 := norm_pos_iff.mp hr
        have hp1 : p ∈ s1.source := by
          simpa only [s0.left_inv hp0] using (hvalid (s0 p)).2 hx
        refine ⟨hp1, ?_⟩
        change ‖s1 p - 0‖ < rMinus
        rw [sub_zero, ← s0.left_inv hp0, hnorm (s0 p) hx]
        apply (div_lt_iff₀ hr).2
        nlinarith [mul_le_mul_of_nonneg_right (le_of_not_gt hlt) hMinus.le]
  have htrans : (c0.symm.trans c1).source =
      {x : E3 | 4 / rMinus < ‖x‖ ∧ ‖x‖ < rPlus} := by
    ext x
    change (x ∈ c0.target ∧ s0.symm x ∈ s1.source ∩ s1 ⁻¹' ball 0 rMinus) ↔ _
    rw [ht0]
    simp only [mem_ball_zero_iff, mem_inter_iff, mem_preimage, hvalid, mem_ofPred_eq]
    constructor
    · rintro ⟨hxPlus, hx, hxMinus⟩
      rw [hnorm x hx] at hxMinus
      refine ⟨(div_lt_iff₀ hMinus).2 ?_, hxPlus⟩
      have h := (div_lt_iff₀ (norm_pos_iff.mpr hx)).1 hxMinus
      nlinarith
    · rintro ⟨hxMinus, hxPlus⟩
      have hr : 0 < ‖x‖ := (div_pos (by norm_num) hMinus).trans hxMinus
      have hx : x ≠ 0 := norm_pos_iff.mp hr
      refine ⟨hxPlus, hx, ?_⟩
      rw [hnorm x hx]
      apply (div_lt_iff₀ hr).2
      have h := (div_lt_iff₀ hMinus).1 hxMinus
      nlinarith
  refine ⟨B, c0, c1, hB, rfl, rfl, rfl, rfl, rfl, rfl, ht0, ht1, hcover,
    ?_, ?_, ?_, ?_, htrans, ?_⟩
  · exact (contMDiffOn_of_mem_maximalAtlas
      (threeSphereStereographic_mem_maximalAtlas v)).mono inter_subset_left
  · exact (contMDiffOn_of_mem_maximalAtlas
      (threeSphereStereographic_mem_maximalAtlas (-v))).mono inter_subset_left
  · exact (contMDiffOn_symm_of_mem_maximalAtlas
      (threeSphereStereographic_mem_maximalAtlas v)).mono inter_subset_left
  · exact (contMDiffOn_symm_of_mem_maximalAtlas
      (threeSphereStereographic_mem_maximalAtlas (-v))).mono inter_subset_left
  · intro x hx
    rw [htrans] at hx
    have hr : 0 < ‖x‖ := (div_pos (by norm_num) hMinus).trans hx.1
    exact hB x (norm_pos_iff.mp hr)

end PoincareConjecture.M25.Topology3D
