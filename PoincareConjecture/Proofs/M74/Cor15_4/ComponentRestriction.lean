import PoincareConjecture.Proofs.M74.Cor15_4.ComponentSourceRestriction
import PoincareConjecture.Proofs.M74.Cor15_4.ComponentTargetRegion
import PoincareConjecture.Proofs.M74.Cor15_4.RegionTargetRestriction










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SmoothConnectedSumData

variable {A B C P Q : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)
  {U : Set A.carrier} {V : Set B.carrier}



noncomputable def selectedFirstEquivalence
    (EA : SurgeryRegionEquivalence P A univ U) (hU : IsOpen U)
    (hfirst : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U) :
    SurgeryRegionEquivalence P C
      (S.first_ball.restrictToRegion EA hU hfirst).closedBallᶜ (S.selectedFirstRegion U) := by
  let E := (EA.puncture S.first_ball hU hfirst).trans
    (S.first_identify.restrictSource (U' := U ∩ S.first_ball.closedBallᶜ) inter_subset_right)
  have himage : S.first_identify.map '' (U ∩ S.first_ball.closedBallᶜ) =
      S.selectedFirstRegion U := by
    rw [S.selectedFirstRegion_eq_image, inter_comm U]
  exact {
    E with
    map_image := E.map_image.trans himage
    inverse_image := by rw [← himage]; exact E.inverse_image
    right_inverse := by rw [← himage]; exact E.right_inverse
    inverse_smooth := by rw [← himage]; exact E.inverse_smooth }



noncomputable def selectedSecondEquivalence
    (EB : SurgeryRegionEquivalence Q B univ V) (hV : IsOpen V)
    (hsecond : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V) :
    SurgeryRegionEquivalence Q C
      (S.second_ball.restrictToRegion EB hV hsecond).closedBallᶜ (S.selectedSecondRegion V) := by
  let E := (EB.puncture S.second_ball hV hsecond).trans
    (S.second_identify.restrictSource (U' := V ∩ S.second_ball.closedBallᶜ) inter_subset_right)
  have himage : S.second_identify.map '' (V ∩ S.second_ball.closedBallᶜ) =
      S.selectedSecondRegion V := by
    rw [S.selectedSecondRegion_eq_image, inter_comm V]
  exact {
    E with
    map_image := E.map_image.trans himage
    inverse_image := by rw [← himage]; exact E.inverse_image
    right_inverse := by rw [← himage]; exact E.right_inverse
    inverse_smooth := by rw [← himage]; exact E.inverse_smooth }



theorem selectedFirstEquivalence_map
    (EA : SurgeryRegionEquivalence P A univ U) (hU : IsOpen U)
    (hfirst : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U) (x : P.carrier) :
    (S.selectedFirstEquivalence EA hU hfirst).map x = S.first_identify.map (EA.map x) := rfl



theorem selectedSecondEquivalence_map
    (EB : SurgeryRegionEquivalence Q B univ V) (hV : IsOpen V)
    (hsecond : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V) (x : Q.carrier) :
    (S.selectedSecondEquivalence EB hV hsecond).map x = S.second_identify.map (EB.map x) := rfl



def selectedComponentOpens (hU : IsClopen U) (hV : IsClopen V)
    (hfirst : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U)
    (hsecond : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V) :
    TopologicalSpace.Opens C.carrier :=
  ⟨S.selectedComponentRegion U V,
    (S.selectedComponentRegion_isClopen hU hV hfirst hsecond).isOpen⟩




noncomputable def restrictComponents
    (EA : SurgeryRegionEquivalence P A univ U)
    (EB : SurgeryRegionEquivalence Q B univ V)
    (hU : IsClopen U) (hV : IsClopen V)
    (hfirst : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U)
    (hsecond : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V) :
    SmoothConnectedSumData P Q
      (C.opens (S.selectedComponentOpens hU hV hfirst hsecond)) := by
  classical
  let T := S.selectedComponentOpens hU hV hfirst hsecond
  have hfirstT : S.selectedFirstRegion U ⊆ T := fun _ hx => Or.inl (Or.inl hx)
  have hsecondT : S.selectedSecondRegion V ⊆ T := fun _ hx => Or.inl (Or.inr hx)
  have hcollarT : MapsTo S.collar (univ ×ˢ Ioo (-1 : ℝ) 1) T := by
    intro x hx
    exact S.collarBand_subset_selectedComponentRegion hfirst hsecond (mem_image_of_mem _ hx)
  have hcentralT (z : UnitTwoSphere) : S.collar (z, 0) ∈ T :=
    Or.inr (mem_image_of_mem _ ⟨mem_univ z, mem_singleton 0⟩)
  let z0 : UnitTwoSphere := Classical.choice
    (NormedSpace.sphere_nonempty (E := StandardCapSpace).mpr zero_le_one).coe_sort
  let y0 : T := ⟨S.collar (z0, 0), hcentralT z0⟩
  let firstE := (S.selectedFirstEquivalence EA hU.isOpen hfirst).restrictOpenTargetOn
    T hfirstT y0
  let secondE := (S.selectedSecondEquivalence EB hV.isOpen hsecond).restrictOpenTargetOn
    T hsecondT y0
  let firstBall := S.first_ball.restrictToRegion EA hU.isOpen hfirst
  let secondBall := S.second_ball.restrictToRegion EB hV.isOpen hsecond
  refine {
    first_ball := firstBall
    second_ball := secondBall
    first_region := Subtype.val ⁻¹' S.selectedFirstRegion U
    second_region := Subtype.val ⁻¹' S.selectedSecondRegion V
    first_open := (S.selectedFirstRegion_open hU.isOpen).preimage continuous_subtype_val
    second_open := (S.selectedSecondRegion_open hV.isOpen).preimage continuous_subtype_val
    first_identify := firstE
    second_identify := secondE
    regions_disjoint := ?_
    sphere_gluing := S.sphere_gluing
    collar := T.liftMap y0 S.collar
    collar_inverse := S.collar_inverse ∘ Subtype.val
    collar_smooth := T.contMDiffOn_liftMap y0 S.collar_smooth hcollarT
    collar_inverse_smooth := ?_
    collar_left_inverse := ?_
    collar_right_inverse := ?_
    collar_open := ?_
    negative_gluing := ?_
    positive_gluing := ?_
    central_disjoint := ?_
    cover := ?_ }
  · exact Set.disjoint_left.mpr (fun _ hx hy =>
      Set.disjoint_left.mp S.regions_disjoint hx.1 hy.1)
  · apply S.collar_inverse_smooth.comp contMDiff_subtype_val.contMDiffOn
    rintro _ ⟨x, hx, rfl⟩
    change (T.liftMap y0 S.collar x).val ∈ S.collar '' (univ ×ˢ Ioo (-1 : ℝ) 1)
    rw [T.liftMap_val_of_mem y0 S.collar (hcollarT hx)]
    exact mem_image_of_mem _ hx
  · intro x hx
    change S.collar_inverse (T.liftMap y0 S.collar x).val = x
    rw [T.liftMap_val_of_mem y0 S.collar (hcollarT hx)]
    exact S.collar_left_inverse hx
  · rintro _ ⟨x, hx, rfl⟩
    change T.liftMap y0 S.collar (S.collar_inverse (T.liftMap y0 S.collar x).val) =
      T.liftMap y0 S.collar x
    rw [T.liftMap_val_of_mem y0 S.collar (hcollarT hx), S.collar_left_inverse hx]
  · change IsOpen (T.liftMap y0 S.collar '' (univ ×ˢ Ioo (-1 : ℝ) 1) : Set T)
    rw [T.liftMap_image y0 S.collar hcollarT]
    exact S.collar_open.preimage continuous_subtype_val
  · intro z s hs
    apply Subtype.ext
    have hr : 1 - s ∈ Ioo (1 : ℝ) 2 := by
      constructor <;> linarith [hs.1, hs.2]
    have hx : (1 - s) • z.val ∈ ball (0 : StandardCapSpace) 2 := by
      simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one hr.1), mem_sphere_zero_iff_norm.mp z.property,
        mul_one] using hr.2
    change (T.liftMap y0 S.collar (z, s)).val =
      (firstE.map (firstBall.map ((1 - s) • z.val))).val
    rw [T.liftMap_val_of_mem y0 S.collar
      (hcollarT ⟨mem_univ z, hs.1, lt_trans hs.2 zero_lt_one⟩)]
    rw [(S.selectedFirstEquivalence EA hU.isOpen hfirst).restrictOpenTargetOn_map_val
      T hfirstT y0 (firstBall.radial_mem_complement z hr)]
    rw [S.selectedFirstEquivalence_map,
      S.first_ball.map_restrictToRegion_map EA hU.isOpen hfirst hx]
    exact S.negative_gluing z s hs
  · intro z s hs
    apply Subtype.ext
    have hr : 1 + s ∈ Ioo (1 : ℝ) 2 := by
      constructor <;> linarith [hs.1, hs.2]
    have hx : (1 + s) • (S.sphere_gluing z).val ∈ ball (0 : StandardCapSpace) 2 := by
      simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one hr.1),
        mem_sphere_zero_iff_norm.mp (S.sphere_gluing z).property, mul_one] using hr.2
    change (T.liftMap y0 S.collar (z, s)).val =
      (secondE.map (secondBall.map ((1 + s) • (S.sphere_gluing z).val))).val
    rw [T.liftMap_val_of_mem y0 S.collar
      (hcollarT ⟨mem_univ z, lt_trans (by norm_num : (-1 : ℝ) < 0) hs.1, hs.2⟩)]
    rw [(S.selectedSecondEquivalence EB hV.isOpen hsecond).restrictOpenTargetOn_map_val
      T hsecondT y0 (secondBall.radial_mem_complement (S.sphere_gluing z) hr)]
    rw [S.selectedSecondEquivalence_map,
      S.second_ball.map_restrictToRegion_map EB hV.isOpen hsecond hx]
    exact S.positive_gluing z s hs
  · apply Set.disjoint_left.mpr
    rintro _ ⟨⟨z, s⟩, hs, rfl⟩ hy
    have hs0 : s = 0 := hs.2
    subst s
    have hyold : (T.liftMap y0 S.collar (z, 0)).val ∈ S.first_region ∪ S.second_region :=
      hy.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    rw [T.liftMap_val_of_mem y0 S.collar (hcentralT z)] at hyold
    exact Set.disjoint_left.mp S.central_disjoint
      (mem_image_of_mem _ ⟨mem_univ z, mem_singleton 0⟩) hyold
  · apply eq_univ_of_forall
    intro x
    have hx : x.val ∈ S.selectedFirstRegion U ∪ S.selectedSecondRegion V ∪
        S.collar '' (univ ×ˢ ({0} : Set ℝ)) := x.property
    rcases hx with (hx | hx) | ⟨⟨z, s⟩, hs, heq⟩
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · have hs0 : s = 0 := hs.2
      subst s
      refine Or.inr ⟨(z, 0), ⟨mem_univ z, mem_singleton 0⟩, ?_⟩
      apply Subtype.ext
      exact (T.liftMap_val_of_mem y0 S.collar (hcentralT z)).trans heq

end PoincareConjecture.SmoothConnectedSumData
