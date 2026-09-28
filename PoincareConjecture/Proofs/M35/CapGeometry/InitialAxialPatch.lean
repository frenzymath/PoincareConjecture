import PoincareConjecture.Proofs.M35.Thm12_28.NeckRestriction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35


noncomputable def cylinderAxialDilation (c : ℝ) (hc : 0 < c) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      StandardCylinderSpace StandardCylinderSpace ∞ where
  toFun z := (z.1, c * z.2)
  invFun z := (z.1, z.2 / c)
  left_inv z := by ext <;> simp [hc.ne']
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact mul_div_cancel₀ z.2 hc.ne'
  contMDiff_toFun := contMDiff_fst.prodMk
    (((contDiff_const.mul contDiff_id).contMDiff).comp contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (((contDiff_id.div_const c).contMDiff).comp contMDiff_snd)

end PoincareConjecture.M35

namespace PoincareConjecture.StandardCylinderPatch



noncomputable def axialRescale {length : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch length x) (c l : ℝ) (hc : 0 < c) (hl : 0 < l)
    (hcl : c * l ≤ length) : StandardCylinderPatch l x := by
  let M := N.restrict (mul_pos hc hl) hcl
  let e := M35.cylinderAxialDilation c hc
  have hmap : MapsTo e (univ ×ˢ Ioo (-l) l) (univ ×ˢ Ioo (-(c * l)) (c * l)) := by
    intro z hz
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -(c * l) < c * z.2
      simpa only [mul_neg] using mul_lt_mul_of_pos_left hz.2.1 hc
    · exact mul_lt_mul_of_pos_left hz.2.2 hc
  have hinv : MapsTo e.symm (univ ×ˢ Ioo (-(c * l)) (c * l))
      (univ ×ˢ Ioo (-l) l) := by
    intro z hz
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -l < z.2 / c
      exact (lt_div_iff₀ hc).mpr (by nlinarith only [hz.2.1])
    · change z.2 / c < l
      exact (div_lt_iff₀ hc).mpr (by nlinarith only [hz.2.2])
  refine {
    length_pos := hl
    carrier := M.carrier
    carrier_open := M.carrier_open
    coordinate := M.coordinate ∘ e
    inverse := e.symm ∘ M.inverse
    coordinate_image := ?_
    coordinate_left_inverse := ?_
    coordinate_right_inverse := ?_
    inverse_domain := ?_
    coordinate_smooth := M.coordinate_smooth.comp e.contMDiff.contMDiffOn hmap
    inverse_smooth := e.symm.contMDiff.comp_contMDiffOn M.inverse_smooth
    center_sphere := ?_
  }
  · apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact M.coordinate_image ▸ mem_image_of_mem M.coordinate (hmap hz)
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := M.coordinate_image.symm ▸ hy
      refine ⟨e.symm z, hinv hz, ?_⟩
      simp only [Function.comp_apply, e.apply_symm_apply]
  · intro z hz
    simp only [Function.comp_apply, M.coordinate_left_inverse (hmap hz), e.symm_apply_apply]
  · intro y hy
    simp only [Function.comp_apply, e.apply_symm_apply, M.coordinate_right_inverse hy]
  · intro y hy
    exact (hinv ⟨mem_univ _, M.inverse_domain y hy⟩).2
  · obtain ⟨q, hq⟩ := M.center_sphere
    refine ⟨q, ?_⟩
    change M.coordinate (q, c * 0) = x
    simpa only [mul_zero] using hq

theorem axialRescale_carrier {length : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch length x) (c l : ℝ) (hc : 0 < c) (hl : 0 < l)
    (hcl : c * l ≤ length) :
    (N.axialRescale c l hc hl hcl).carrier =
      N.carrier ∩ N.inverse ⁻¹' (univ ×ˢ Ioo (-(c * l)) (c * l)) := rfl

theorem axialRescale_coordinate {length : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch length x) (c l : ℝ) (hc : 0 < c) (hl : 0 < l)
    (hcl : c * l ≤ length) (z : StandardCylinderSpace) :
    (N.axialRescale c l hc hl hcl).coordinate z = N.coordinate (z.1, c * z.2) := rfl

theorem axialRescale_subset {length : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch length x) (c l : ℝ) (hc : 0 < c) (hl : 0 < l)
    (hcl : c * l ≤ length) : (N.axialRescale c l hc hl hcl).carrier ⊆ N.carrier :=
  inter_subset_left

end PoincareConjecture.StandardCylinderPatch
