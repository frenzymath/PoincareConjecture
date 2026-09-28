import PoincareConjecture.Proofs.M38.NeckCoordinates










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]


theorem limit_inverse_mem (x : (F.event T hT).terminal.carrier) :
    (F.event T hT).limit_identify.inverse x ∈ (F.event T hT).regular_limit := by
  exact (F.event T hT).limit_identify.inverse_image.subset
    (Set.mem_image_of_mem _ (Set.mem_univ x))


def limitInverseHomeomorph :
    (F.event T hT).terminal.carrier ≃ₜ (F.event T hT).regular_limit where
  toFun := fun x => ⟨(F.event T hT).limit_identify.inverse x,
    limit_inverse_mem F T hT x⟩
  invFun := fun x => (F.event T hT).limit_identify.map x.1
  left_inv := fun x => (F.event T hT).limit_identify.right_inverse (Set.mem_univ x)
  right_inv := fun x => Subtype.ext ((F.event T hT).limit_identify.left_inverse x.2)
  continuous_toFun := (limit_inverse_continuous F T hT).subtype_mk _
  continuous_invFun := (F.event T hT).limit_identify.map_smooth.continuousOn.domRestrict


theorem limit_inverse_openEmbedding :
    Topology.IsOpenEmbedding (F.event T hT).limit_identify.inverse :=
  (F.event T hT).regular_limit_open.isOpenEmbedding_subtypeVal.comp
    (limitInverseHomeomorph F T hT).isOpenEmbedding


def eventCollarMap (i : Fin (F.event T hT).cap_count) :
    RoundCylinderSpace → (F.slice (F.event T hT).tMinus).carrier :=
  (F.event T hT).limit_identify.inverse ∘ ((F.event T hT).necks i).neck.coordinate_map


def eventCollarInverse (i : Fin (F.event T hT).cap_count) :
    (F.slice (F.event T hT).tMinus).carrier → RoundCylinderSpace :=
  ((F.event T hT).necks i).neck.coordinate_inverse ∘ (F.event T hT).limit_identify.map


theorem event_collar_smooth (i : Fin (F.event T hT).cap_count) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (eventCollarMap F T hT i)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
  (contMDiffOn_univ.mp (F.event T hT).limit_identify.inverse_smooth).comp_contMDiffOn
    (((F.event T hT).necks i).neck.coordinate_map_smooth.mono (neck_unit_domain _))


theorem event_collar_left_inverse (i : Fin (F.event T hT).cap_count) :
    Set.LeftInvOn (eventCollarInverse F T hT i) (eventCollarMap F T hT i)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  intro z hz
  change ((F.event T hT).necks i).neck.coordinate_inverse
    ((F.event T hT).limit_identify.map ((F.event T hT).limit_identify.inverse
      (((F.event T hT).necks i).neck.coordinate_map z))) = z
  rw [(F.event T hT).limit_identify.right_inverse (Set.mem_univ _)]
  exact neck_coordinate_inverse_map _ (neck_unit_domain _ hz)


theorem event_collar_right_inverse (i : Fin (F.event T hT).cap_count) :
    Set.LeftInvOn (eventCollarMap F T hT i) (eventCollarInverse F T hT i)
      (eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rintro x ⟨z, hz, rfl⟩
  exact congrArg (eventCollarMap F T hT i) (event_collar_left_inverse F T hT i hz)


theorem event_collar_inverse_smooth (i : Fin (F.event T hT).cap_count) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (eventCollarInverse F T hT i)
      (eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  have hregular : eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) ⊆
      (F.event T hT).regular_limit := by
    rintro x ⟨z, _, rfl⟩
    exact limit_inverse_mem F T hT _
  apply ((F.event T hT).necks i).neck.coordinate_inverse_smooth.comp
    ((F.event T hT).limit_identify.map_smooth.mono hregular)
  rintro x ⟨z, hz, rfl⟩
  change (F.event T hT).limit_identify.map ((F.event T hT).limit_identify.inverse
    (((F.event T hT).necks i).neck.coordinate_map z)) ∈
      ((F.event T hT).necks i).neck.carrier
  rw [(F.event T hT).limit_identify.right_inverse (Set.mem_univ _)]
  exact neck_coordinate_mem _ (neck_unit_domain _ hz)


theorem event_collar_open_on (i : Fin (F.event T hT).cap_count)
    {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (hsub : U ⊆ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    IsOpen (eventCollarMap F T hT i '' U) := by
  change IsOpen (((F.event T hT).limit_identify.inverse ∘
    ((F.event T hT).necks i).neck.coordinate_map) '' U)
  rw [Set.image_comp]
  exact (limit_inverse_openEmbedding F T hT).isOpenMap _
    (neck_coordinate_image_open _ hU (hsub.trans (neck_unit_domain _)))


theorem event_collar_central (i : Fin (F.event T hT).cap_count) :
    eventCollarMap F T hT i '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      (F.event T hT).limit_identify.inverse ''
        ((F.event T hT).necks i).neck.central_sphere := by
  change ((F.event T hT).limit_identify.inverse ∘
    ((F.event T hT).necks i).neck.coordinate_map) '' _ = _
  rw [Set.image_comp, ← ((F.event T hT).necks i).neck.central_sphere_eq]


theorem event_collar_negative_retained (i : Fin (F.event T hT).cap_count) :
    eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) ⊆
      interior (F.event T hT).retained_pre := by
  have hsub : (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (-1 : ℝ) 0 ⊆
      Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans zero_lt_one⟩
  have hopen := event_collar_open_on F T hT i (isOpen_univ.prod isOpen_Ioo) hsub
  apply hopen.subset_interior_iff.mpr
  rintro x ⟨z, hz, rfl⟩
  have hdomain := neck_unit_domain ((F.event T hT).necks i).neck (hsub hz)
  have hregion : ((F.event T hT).necks i).neck.coordinate_map z ∈
      ((F.event T hT).necks i).neck.region (-((F.event T hT).necks i).neck.epsilon⁻¹) 0 := by
    refine ⟨neck_coordinate_mem _ hdomain, ?_, ?_⟩
    · rw [neck_coordinate_inverse_map _ hdomain]
      exact hdomain.2.1
    · rw [neck_coordinate_inverse_map _ hdomain]
      exact hz.2.2
  obtain ⟨y, hy, heq⟩ := (F.event T hT).neck_negative_retained i hregion
  change (F.event T hT).limit_identify.inverse
    (((F.event T hT).necks i).neck.coordinate_map z) ∈ (F.event T hT).retained_pre
  rw [← heq, (F.event T hT).limit_identify.left_inverse
    ((F.event T hT).retained_pre_subset hy)]
  exact hy


theorem event_collar_positive_discarded (i : Fin (F.event T hT).cap_count) :
    Disjoint (eventCollarMap F T hT i '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1))
      (F.event T hT).retained_pre := by
  apply Set.disjoint_left.mpr
  rintro x ⟨z, hz, rfl⟩ hretained
  have hdomain := neck_unit_domain ((F.event T hT).necks i).neck
    ⟨hz.1, (neg_one_lt_zero.trans hz.2.1), hz.2.2⟩
  have hregion : ((F.event T hT).necks i).neck.coordinate_map z ∈
      ((F.event T hT).necks i).neck.region 0 ((F.event T hT).necks i).neck.epsilon⁻¹ := by
    refine ⟨neck_coordinate_mem _ hdomain, ?_, ?_⟩
    · rw [neck_coordinate_inverse_map _ hdomain]
      exact hz.2.1
    · rw [neck_coordinate_inverse_map _ hdomain]
      exact hdomain.2.2
  have hmem : ((F.event T hT).necks i).neck.coordinate_map z ∈
      (F.event T hT).limit_identify.map '' (F.event T hT).retained_pre :=
    ⟨eventCollarMap F T hT i z, hretained,
      (F.event T hT).limit_identify.right_inverse (Set.mem_univ _)⟩
  exact Set.disjoint_left.mp ((F.event T hT).neck_positive_discarded i) hregion hmem

end PoincareConjecture.M38
