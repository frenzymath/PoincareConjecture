import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Patches

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

def M45CylinderPatch.neckHomeomorph {S : GeneralizedSliceCarrier.{u}}
    {eta : ℝ} {x : S.carrier} (P : M45CylinderPatch S eta⁻¹ x) :
    NeckDomain eta ≃ₜ P.carrier where
  toFun z := ⟨P.coordinate (z.1, z.2.1), by
    rw [← P.coordinate_image]
    exact ⟨(z.1, z.2.1), ⟨Set.mem_univ _, z.2.2⟩, rfl⟩⟩
  invFun y := ((P.inverse y.1).1, ⟨(P.inverse y.1).2, P.inverse_domain y.1 y.2⟩)
  left_inv z := by
    have h := P.coordinate_left_inverse
      (show (z.1, z.2.1) ∈ Set.univ ×ˢ Set.Ioo (-eta⁻¹) eta⁻¹ from
        ⟨Set.mem_univ z.1, z.2.2⟩)
    apply Prod.ext
    · change (P.inverse (P.coordinate (z.1, z.2.1))).1 = z.1
      exact congrArg (fun q : RoundCylinderSpace => q.1) h
    · apply Subtype.ext
      change (P.inverse (P.coordinate (z.1, z.2.1))).2 = z.2.1
      exact congrArg (fun q : RoundCylinderSpace => q.2) h
  right_inv y := Subtype.ext (P.coordinate_right_inverse y.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact P.coordinate_smooth.continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨Set.mem_univ z.1, z.2.2⟩)
  continuous_invFun := by
    have h := P.inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
      (fun y : P.carrier => y.2)
    exact h.fst.prodMk (h.snd.subtype_mk _)

noncomputable def M45NeckGluingInput.recentNeck {epsilon beta : ℝ}
    (I : M45NeckGluingInput.{u} epsilon beta)
    (hpos : 0 < beta * epsilon) (hsmall : beta * epsilon < 1 / 2) :
    EpsilonNeck (I.recent_flow.metric 0) where
  epsilon := beta * epsilon
  epsilon_pos := hpos
  epsilon_lt_half := hsmall
  scale := 1
  scale_pos := by norm_num
  center := I.center
  connection := I.recent_flow.connection 0
  scalar_center_pos := by rw [I.final_scalar_one]; norm_num
  scale_eq_scalar := by rw [I.final_scalar_one]; simp
  carrier := I.recent_patch.carrier
  carrier_open := I.recent_patch.carrier_open
  coordinate := I.recent_patch.neckHomeomorph
  coordinate_map := I.recent_patch.coordinate
  coordinate_map_eq := fun _ => rfl
  coordinate_map_smooth := I.recent_patch.coordinate_smooth
  coordinate_inverse := I.recent_patch.inverse
  coordinate_inverse_mem := fun y hy => ⟨Set.mem_univ _, I.recent_patch.inverse_domain y hy⟩
  coordinate_inverse_left := fun z =>
    I.recent_patch.coordinate_left_inverse ⟨Set.mem_univ z.1, z.2.2⟩
  coordinate_inverse_right := fun y hy => Subtype.ext (I.recent_patch.coordinate_right_inverse hy)
  coordinate_inverse_smooth := I.recent_patch.inverse_smooth
  central_sphere := I.recent_patch.coordinate '' (Set.univ ×ˢ ({0} : Set ℝ))
  central_sphere_eq := rfl
  center_on_central_sphere := by
    obtain ⟨z, hz⟩ := I.recent_patch.center_sphere
    exact ⟨(z, 0), ⟨Set.mem_univ _, rfl⟩, hz⟩
  central_sphere_subset := by
    rintro y ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    rw [hs0, ← I.recent_patch.coordinate_image]
    exact ⟨(z, 0), ⟨Set.mem_univ _, by
      constructor <;> linarith [I.recent_patch.length_pos]⟩, rfl⟩
  metric_comparison := ⟨by
    have hzero : 0 ∈ Set.Icc (-I.recent_duration) (0 : ℝ) :=
      ⟨by linarith [I.recent_duration_pos], le_rfl⟩
    obtain ⟨hsmooth, bound, hbound, hjet⟩ := I.recent_comparison
    simpa only [inv_one, one_pow, one_mul] using
      (show RoundCylinderClose (beta * epsilon) 0
        (roundCylinderPullback (I.recent_flow.metric 0) I.recent_patch.coordinate) from
        ⟨hsmooth 0 hzero, bound, hbound, hjet 0 hzero⟩)⟩

end PoincareConjecture
