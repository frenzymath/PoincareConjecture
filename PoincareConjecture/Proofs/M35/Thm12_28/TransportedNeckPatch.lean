import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCoordinates










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



noncomputable def coordinatePartialDiffeomorph (N : EpsilonNeck g) :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace M ∞ where
  toFun := N.coordinate_map
  invFun := N.coordinate_inverse
  source := univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
  target := N.carrier
  map_source' z hz := (N.coordinate_map_eq (z.1, ⟨z.2, hz.2⟩)) ▸
    (N.coordinate (z.1, ⟨z.2, hz.2⟩)).property
  map_target' := N.coordinate_inverse_mem
  left_inv' z hz := (congrArg N.coordinate_inverse
    (N.coordinate_map_eq (z.1, ⟨z.2, hz.2⟩)).symm).trans
      (N.coordinate_inverse_left (z.1, ⟨z.2, hz.2⟩))
  right_inv' x hx := (N.coordinate_map_eq ((N.coordinate_inverse x).1,
    ⟨(N.coordinate_inverse x).2, (N.coordinate_inverse_mem x hx).2⟩)).symm.trans
      (congrArg Subtype.val (N.coordinate_inverse_right x hx))
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := N.carrier_open
  contMDiffOn_toFun := N.coordinate_map_smooth
  contMDiffOn_invFun := N.coordinate_inverse_smooth



noncomputable def transportedStandardPatch (N : EpsilonNeck g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) M StandardCapSpace ∞)
    (hsub : N.carrier ⊆ f.source) :
    StandardCylinderPatch N.epsilon⁻¹ (f N.center) := by
  let e := N.coordinatePartialDiffeomorph.trans f
  have hsource : e.source = univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    apply inter_eq_left.mpr
    intro z hz
    exact hsub (N.coordinatePartialDiffeomorph.map_source hz)
  refine {
    length_pos := inv_pos.mpr N.epsilon_pos
    carrier := e.target
    carrier_open := e.open_target
    coordinate := e
    inverse := e.symm
    coordinate_image := ?_
    coordinate_left_inverse := ?_
    coordinate_right_inverse := fun _ hy => e.right_inv hy
    inverse_domain := ?_
    coordinate_smooth := hsource ▸ e.contMDiffOn_toFun
    inverse_smooth := e.contMDiffOn_invFun
    center_sphere := ?_
  }
  · exact hsource ▸ e.toOpenPartialHomeomorph.image_source_eq_target
  · intro z hz
    exact e.left_inv (hsource.symm ▸ hz)
  · intro y hy
    exact (hsource ▸ e.map_target hy).2
  · obtain ⟨z, hz, hcenter⟩ := N.central_sphere_eq ▸ N.center_on_central_sphere
    refine ⟨z.1, ?_⟩
    change f (N.coordinate_map (z.1, 0)) = f N.center
    apply congrArg f
    exact (congrArg (fun s : ℝ => N.coordinate_map (z.1, s)) hz.2.symm).trans hcenter

end PoincareConjecture.EpsilonNeck
