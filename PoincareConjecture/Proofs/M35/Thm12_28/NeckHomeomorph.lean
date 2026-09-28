import PoincareConjecture.Definitions.M35StandardCapUniqueness









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.StandardCylinderPatch



noncomputable def coordinateHomeomorph {epsilon : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) : NeckDomain epsilon ≃ₜ N.carrier where
  toFun z := ⟨N.coordinate (z.1, z.2.val), by
    rw [← N.coordinate_image]
    exact ⟨(z.1, z.2.val), ⟨mem_univ _, z.2.property⟩, rfl⟩⟩
  invFun y := ((N.inverse y.val).1, ⟨(N.inverse y.val).2, N.inverse_domain y.val y.property⟩)
  left_inv z := by
    have h := N.coordinate_left_inverse (show (z.1, z.2.val) ∈
      univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ from ⟨mem_univ _, z.2.property⟩)
    apply Prod.ext
    · change (N.inverse (N.coordinate (z.1, z.2.val))).1 = z.1
      exact congrArg (fun p : StandardCylinderSpace => p.1) h
    · apply Subtype.ext
      change (N.inverse (N.coordinate (z.1, z.2.val))).2 = z.2.val
      exact congrArg (fun p : StandardCylinderSpace => p.2) h
  right_inv y := Subtype.ext (N.coordinate_right_inverse y.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact N.coordinate_smooth.continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨mem_univ _, z.2.property⟩)
  continuous_invFun := by
    have h := N.inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
      (fun y : N.carrier => y.property)
    exact h.fst.prodMk (h.snd.subtype_mk _)

end PoincareConjecture.StandardCylinderPatch
