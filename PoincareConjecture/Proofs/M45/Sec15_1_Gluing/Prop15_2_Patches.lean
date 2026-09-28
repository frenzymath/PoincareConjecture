import PoincareConjecture.Definitions.M45NeckGluing









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace M45CylinderPatch

variable {S : GeneralizedSliceCarrier.{u}} {length : ℝ} {center : S.carrier}



theorem center_mem (P : M45CylinderPatch S length center) : center ∈ P.carrier := by
  obtain ⟨q, hq⟩ := P.center_sphere
  rw [← P.coordinate_image]
  exact ⟨(q, 0), ⟨Set.mem_univ _, neg_lt_zero.mpr P.length_pos, P.length_pos⟩, hq⟩



noncomputable def restrict (P : M45CylinderPatch S length center)
    (radius : ℝ) (hradius : 0 < radius) (hle : radius ≤ length) :
    M45CylinderPatch S radius center where
  length_pos := hradius
  carrier := P.carrier ∩ P.inverse ⁻¹' (Set.univ ×ˢ Set.Ioo (-radius) radius)
  carrier_open := P.inverse_smooth.continuousOn.isOpen_inter_preimage
    P.carrier_open (isOpen_univ.prod isOpen_Ioo)
  coordinate := P.coordinate
  inverse := P.inverse
  coordinate_image := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ Set.univ ×ˢ Set.Ioo (-length) length :=
        ⟨hz.1, lt_of_le_of_lt (neg_le_neg hle) hz.2.1, lt_of_lt_of_le hz.2.2 hle⟩
      refine ⟨?_, ?_⟩
      · rw [← P.coordinate_image]
        exact Set.mem_image_of_mem P.coordinate hz'
      · simpa only [Set.mem_preimage, P.coordinate_left_inverse hz'] using hz
    · intro hx
      refine ⟨P.inverse x, hx.2, P.coordinate_right_inverse hx.1⟩
  coordinate_left_inverse := fun z hz => P.coordinate_left_inverse
    ⟨hz.1, lt_of_le_of_lt (neg_le_neg hle) hz.2.1, lt_of_lt_of_le hz.2.2 hle⟩
  coordinate_right_inverse := fun x hx => P.coordinate_right_inverse hx.1
  inverse_domain := fun x hx => hx.2.2
  coordinate_smooth := P.coordinate_smooth.mono fun z hz =>
    ⟨hz.1, lt_of_le_of_lt (neg_le_neg hle) hz.2.1, lt_of_lt_of_le hz.2.2 hle⟩
  inverse_smooth := P.inverse_smooth.mono Set.inter_subset_left
  center_sphere := P.center_sphere



theorem restrict_subset (P : M45CylinderPatch S length center)
    (radius : ℝ) (hradius : 0 < radius) (hle : radius ≤ length) :
    (P.restrict radius hradius hle).carrier ⊆ P.carrier :=
  Set.inter_subset_left

end M45CylinderPatch

namespace M45NeckGluingInput

variable {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)




theorem older_duration_ge :
    I.recent_duration + I.older_neck.neck.scale ^ 2 ≤ I.older_duration := by
  have hs : -I.recent_duration - I.older_neck.neck.scale ^ 2 <
      -I.recent_duration := by nlinarith [sq_pos_of_pos I.older_neck.neck.scale_pos]
  have h := (Set.Ioc_subset_Ioc_iff hs).mp I.older_neck.backward_subset
  linarith [h.2]



theorem older_survival_of_duration (h : 1 ≤ I.older_duration) :
    ∀ t ∈ Set.Ioc (-1 : ℝ) 0, t < -I.recent_duration →
      t ∈ Set.Ioc (-I.older_duration) (-I.recent_duration) := by
  intro t ht hrecent
  exact ⟨lt_of_le_of_lt (neg_le_neg h) ht.1, hrecent.le⟩



theorem older_survival_of_scale (h : 1 ≤ I.older_neck.neck.scale ^ 2) :
    ∀ t ∈ Set.Ioc (-1 : ℝ) 0, t < -I.recent_duration →
      t ∈ Set.Ioc (-I.older_duration) (-I.recent_duration) := by
  apply I.older_survival_of_duration
  linarith [I.older_duration_ge, I.recent_duration_pos]




theorem joining_pullback (z : RoundCylinderSpace)
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback (I.older_flow.metric (-I.recent_duration))
        (I.identify ∘ I.recent_patch.coordinate) z v w =
      roundCylinderPullback (I.recent_flow.metric (-I.recent_duration))
        I.recent_patch.coordinate z v w := by
  have hx : I.recent_patch.coordinate z ∈ I.recent_patch.carrier := by
    rw [← I.recent_patch.coordinate_image]
    exact Set.mem_image_of_mem _ hz
  have hc := I.recent_patch.coordinate_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
  have hi := I.identify_smooth.contMDiffAt (I.recent_patch.carrier_open.mem_nhds hx)
  unfold roundCylinderPullback
  rw [mfderiv_comp z (hi.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
  exact I.joining_metric _ hx _ _

end M45NeckGluingInput

end PoincareConjecture
