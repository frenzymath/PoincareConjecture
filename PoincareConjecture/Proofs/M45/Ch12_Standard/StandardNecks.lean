import PoincareConjecture.Definitions.Ch12.StandardCap









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture



def StandardCylinderPatch.neckHomeomorph {epsilon : ℝ} {x : StandardCapSpace}
    (P : StandardCylinderPatch epsilon⁻¹ x) : NeckDomain epsilon ≃ₜ P.carrier where
  toFun z := ⟨P.coordinate (z.1, z.2.1), by
    rw [← P.coordinate_image]
    exact ⟨(z.1, z.2.1), ⟨Set.mem_univ _, z.2.2⟩, rfl⟩⟩
  invFun y := ((P.inverse y.1).1, ⟨(P.inverse y.1).2, P.inverse_domain y.1 y.2⟩)
  left_inv z := by
    have h := P.coordinate_left_inverse
      (show (z.1, z.2.1) ∈ Set.univ ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ from
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



noncomputable def StandardStaticNeck.toEpsilonNeck
    {atlas : StandardCylinderAtlas} {g : RiemannianMetric 3 StandardCapSpace}
    {D : LeviCivitaData g} {epsilon : ℝ} (N : StandardStaticNeck atlas g D epsilon) :
    EpsilonNeck g where
  epsilon := epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := N.epsilon_lt_half
  scale := D.scalarCurvature N.center ^ (-1 / 2 : ℝ)
  scale_pos := Real.rpow_pos_of_pos N.scalar_pos _
  center := N.center
  connection := D
  scalar_center_pos := N.scalar_pos
  scale_eq_scalar := rfl
  carrier := N.patch.carrier
  carrier_open := N.patch.carrier_open
  coordinate := N.patch.neckHomeomorph
  coordinate_map := N.patch.coordinate
  coordinate_map_eq := fun _ => rfl
  coordinate_map_smooth := N.patch.coordinate_smooth
  coordinate_inverse := N.patch.inverse
  coordinate_inverse_mem := fun y hy => ⟨Set.mem_univ _, N.patch.inverse_domain y hy⟩
  coordinate_inverse_left := fun z =>
    N.patch.coordinate_left_inverse ⟨Set.mem_univ z.1, z.2.2⟩
  coordinate_inverse_right := fun y hy => Subtype.ext (N.patch.coordinate_right_inverse hy)
  coordinate_inverse_smooth := N.patch.inverse_smooth
  central_sphere := N.patch.centralSphere
  central_sphere_eq := rfl
  center_on_central_sphere := by
    obtain ⟨z, hz⟩ := N.patch.center_sphere
    exact ⟨(z, 0), ⟨Set.mem_univ _, rfl⟩, hz⟩
  central_sphere_subset := by
    rintro y ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    rw [hs0, ← N.patch.coordinate_image]
    exact ⟨(z, 0), ⟨Set.mem_univ _, by
      constructor <;> linarith [N.patch.length_pos]⟩, rfl⟩
  metric_comparison := ⟨by
    have hscale : (D.scalarCurvature N.center ^ (-1 / 2 : ℝ))⁻¹ ^ 2 =
        D.scalarCurvature N.center := by
      rw [inv_pow, ← Real.rpow_mul_natCast N.scalar_pos.le (-1 / 2) 2]
      norm_num [Real.rpow_neg_one]
    simpa only [StandardSpatialCylinderClose, hscale] using N.close⟩



def StandardEvolvingNeck.staticAtZero
    {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t epsilon : ℝ} {x : StandardCapSpace}
    {I : Set ℝ} (N : StandardEvolvingNeck atlas F t epsilon x I) (hzero : 0 ∈ I) :
    StandardStaticNeck atlas (F.metric t) (F.connection t) epsilon where
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := N.epsilon_lt_half
  center := x
  scalar_pos := N.scalar_pos
  patch := N.patch
  close := by
    obtain ⟨hsmooth, bound, hbound, hclose⟩ := N.close
    refine ⟨?_, bound, hbound, ?_⟩
    · simpa only [zero_div, add_zero] using hsmooth 0 hzero
    · simpa only [zero_div, add_zero] using hclose 0 hzero

end PoincareConjecture
