import PoincareConjecture.Proofs.M74.Cor15_4.ComponentSourceRestriction
import PoincareConjecture.Proofs.M74.Cor15_4.ComponentTargetRegion

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SmoothConnectedSumData

variable {A B C P : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)

theorem selectedFirstRegion_isClopen_of_disjoint_chart {W : Set A.carrier}
    (hW : IsClopen W)
    (hdisjoint : Disjoint W (S.first_ball.map '' ball (0 : StandardCapSpace) 2)) :
    IsClopen (S.selectedFirstRegion W) := by
  have hchart : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ Wᶜ := by
    intro x hx hxW
    exact Set.disjoint_left.mp hdisjoint hxW hx
  have h := (S.selectedComponentRegion_isClopen hW.compl isClopen_univ
    hchart (subset_univ _)).compl
  rw [S.selectedComponentRegion_compl] at h
  simpa only [compl_compl, compl_univ, selectedSecondRegion, preimage_empty,
    inter_empty, union_empty] using h

theorem selectedSecondRegion_isClopen_of_disjoint_chart {W : Set B.carrier}
    (hW : IsClopen W)
    (hdisjoint : Disjoint W (S.second_ball.map '' ball (0 : StandardCapSpace) 2)) :
    IsClopen (S.selectedSecondRegion W) := by
  have hchart : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ Wᶜ := by
    intro x hx hxW
    exact Set.disjoint_left.mp hdisjoint hxW hx
  have h := (S.selectedComponentRegion_isClopen isClopen_univ hW.compl
    (subset_univ _) hchart).compl
  rw [S.selectedComponentRegion_compl] at h
  simpa only [compl_compl, compl_univ, selectedFirstRegion, preimage_empty,
    inter_empty, empty_union] using h

noncomputable def firstUntouchedEquivalence {W : Set A.carrier}
    (E : SurgeryRegionEquivalence P A univ W)
    (hdisjoint : Disjoint W (S.first_ball.map '' ball (0 : StandardCapSpace) 2)) :
    SurgeryRegionEquivalence P C univ (S.selectedFirstRegion W) := by
  have hWball : W ⊆ S.first_ball.closedBallᶜ := by
    intro x hx hxball
    exact Set.disjoint_left.mp hdisjoint hx
      (S.first_ball.closedBall_subset_of_chart_subset (Subset.rfl) hxball)
  let F := E.trans (S.first_identify.restrictSource hWball)
  have himage : S.first_identify.map '' W = S.selectedFirstRegion W := by
    rw [S.selectedFirstRegion_eq_image, inter_eq_right.mpr hWball]
  exact {
    F with
    map_image := F.map_image.trans himage
    inverse_image := by rw [← himage]; exact F.inverse_image
    right_inverse := by rw [← himage]; exact F.right_inverse
    inverse_smooth := by rw [← himage]; exact F.inverse_smooth }

noncomputable def secondUntouchedEquivalence {W : Set B.carrier}
    (E : SurgeryRegionEquivalence P B univ W)
    (hdisjoint : Disjoint W (S.second_ball.map '' ball (0 : StandardCapSpace) 2)) :
    SurgeryRegionEquivalence P C univ (S.selectedSecondRegion W) := by
  have hWball : W ⊆ S.second_ball.closedBallᶜ := by
    intro x hx hxball
    exact Set.disjoint_left.mp hdisjoint hx
      (S.second_ball.closedBall_subset_of_chart_subset (Subset.rfl) hxball)
  let F := E.trans (S.second_identify.restrictSource hWball)
  have himage : S.second_identify.map '' W = S.selectedSecondRegion W := by
    rw [S.selectedSecondRegion_eq_image, inter_eq_right.mpr hWball]
  exact {
    F with
    map_image := F.map_image.trans himage
    inverse_image := by rw [← himage]; exact F.inverse_image
    right_inverse := by rw [← himage]; exact F.right_inverse
    inverse_smooth := by rw [← himage]; exact F.inverse_smooth }

end PoincareConjecture.SmoothConnectedSumData
