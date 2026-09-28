import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalSheetIntervals
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

structure SignedJointCross (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  disk : Set E
  rim : Set E
  coordinate : Fin 2 → E → ℝ
  center : E
  endpoint : Fin 2 → Bool → E
  disk_ball : IsFinitePLBallPair (ℝ × ℝ) disk rim
  coordinate_continuous : ∀ j, ContinuousOn (coordinate j) disk
  axis_ball : ∀ j, IsFinitePLBallPair ℝ (disk ∩ {z | coordinate j z = 0})
    {endpoint j false, endpoint j true}
  center_interior : ∀ j, center ∈ (disk ∩ {z | coordinate j z = 0}) \
    {endpoint j false, endpoint j true}
  rim_zero : ∀ j, rim ∩ {z | coordinate j z = 0} = {endpoint j false, endpoint j true}
  axes_intersection : (disk ∩ {z | coordinate 0 z = 0}) ∩
    (disk ∩ {z | coordinate 1 z = 0}) = {center}
  endpoint_sign : ∀ (j : Fin 2) (b : Bool), if b then 0 < coordinate j.rev (endpoint j b)
    else coordinate j.rev (endpoint j b) < 0
  axis_radii : ∀ j, disk ∩ {z | coordinate j z = 0} =
    segment ℝ center (endpoint j false) ∪ segment ℝ center (endpoint j true)

namespace SignedJointCross

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (J : SignedJointCross E)

def axis (j : Fin 2) : Set E := J.disk ∩ {z | J.coordinate j z = 0}
def radius (j : Fin 2) (b : Bool) : Set E := segment ℝ J.center (J.endpoint j b)
def side (b : Bool) (v : ℝ) : Prop := if b then 0 ≤ v else v ≤ 0
def quarter (b c : Bool) : Set E :=
  {z | z ∈ J.disk ∧ side b (J.coordinate 0 z) ∧ side c (J.coordinate 1 z)}

theorem endpoint_ne_center (j : Fin 2) (b : Bool) : J.endpoint j b ≠ J.center := by
  intro h
  apply (J.center_interior j).2
  cases b
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem endpoints_ne (j : Fin 2) : J.endpoint j false ≠ J.endpoint j true := by
  intro h
  have hn := J.endpoint_sign j false
  have hp := J.endpoint_sign j true
  change J.coordinate j.rev (J.endpoint j false) < 0 at hn
  change 0 < J.coordinate j.rev (J.endpoint j true) at hp
  rw [h] at hn
  exact (not_lt_of_gt hp) hn

theorem radius_subset_axis (j : Fin 2) (b : Bool) : J.radius j b ⊆ J.axis j := by
  rw [axis, J.axis_radii j]
  cases b
  · exact subset_union_left
  · exact subset_union_right

theorem radius_ball [FiniteDimensional ℝ E] (j : Fin 2) (b : Bool) :
    IsFinitePLBallPair ℝ (J.radius j b) {J.center, J.endpoint j b} := by
  have hb := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).affine_image
    (ContinuousAffineMap.lineMap J.center (J.endpoint j b))
    (AffineMap.lineMap_injective ℝ (J.endpoint_ne_center j b).symm).injOn
  change IsFinitePLBallPair ℝ ((AffineMap.lineMap J.center (J.endpoint j b)) '' Icc (0 : ℝ) 1)
    ((AffineMap.lineMap J.center (J.endpoint j b)) '' ({0, 1} : Set ℝ)) at hb
  rw [← segment_eq_image_lineMap, image_pair, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] at hb
  exact hb

theorem center_zero (j : Fin 2) : J.coordinate j J.center = 0 :=
  (J.center_interior j).1.2

theorem endpoint_mem_rim (j : Fin 2) (b : Bool) : J.endpoint j b ∈ J.rim := by
  apply ((J.rim_zero j).symm.subset ?_).1
  cases b <;> simp

theorem radius_cross_zero (j : Fin 2) (b : Bool) :
    J.radius j b ∩ {z | J.coordinate j.rev z = 0} ⊆ {J.center} := by
  intro z hz
  have hzj := J.radius_subset_axis j b hz.1
  have hzrev : z ∈ J.axis j.rev := ⟨hzj.1, hz.2⟩
  fin_cases j
  · exact J.axes_intersection.subset ⟨hzj, hzrev⟩
  · exact J.axes_intersection.subset ⟨hzrev, hzj⟩

theorem radius_side [FiniteDimensional ℝ E] (j : Fin 2) (b : Bool) :
    ∀ z ∈ J.radius j b, side b (J.coordinate j.rev z) := by
  have hz : J.radius j b ∩ {z | J.coordinate j.rev z = 0} ⊆
      {J.center, J.endpoint j b} := fun z hz => Or.inl (J.radius_cross_zero j b hz)
  have hcont := (J.coordinate_continuous j.rev).mono
    ((J.radius_subset_axis j b).trans inter_subset_left)
  cases b
  · exact (J.radius_ball j false).mapsTo_nonpos_of_zeros_in_boundary _ hcont hz
      ⟨J.endpoint j false, right_mem_segment ℝ _ _, J.endpoint_sign j false⟩
  · exact (J.radius_ball j true).mapsTo_nonneg_of_zeros_in_boundary _ hcont hz
      ⟨J.endpoint j true, right_mem_segment ℝ _ _, J.endpoint_sign j true⟩

theorem radius_cut [FiniteDimensional ℝ E] (j : Fin 2) (b : Bool) :
    J.radius j b = J.axis j ∩ {z | side b (J.coordinate j.rev z)} := by
  apply Subset.antisymm
  · exact fun z hz => ⟨J.radius_subset_axis j b hz, J.radius_side j b z hz⟩
  · rintro z ⟨hz, hsign⟩
    rcases (J.axis_radii j).subset hz with hn | hp
    · cases b
      · exact hn
      · have he := J.radius_cross_zero j false
          ⟨hn, le_antisymm (J.radius_side j false z hn) hsign⟩
        exact he.symm ▸ left_mem_segment ℝ _ _
    · cases b
      · have he := J.radius_cross_zero j true
          ⟨hp, le_antisymm hsign (J.radius_side j true z hp)⟩
        exact he.symm ▸ left_mem_segment ℝ _ _
      · exact hp

theorem radius_rim [FiniteDimensional ℝ E] (j : Fin 2) (b : Bool) :
    J.radius j b ∩ J.rim = {J.endpoint j b} := by
  apply Subset.antisymm
  · rintro z ⟨hz, hzq⟩
    have hends := (J.rim_zero j).subset ⟨hzq, (J.radius_subset_axis j b hz).2⟩
    rcases hends with hn | hp
    · cases b
      · exact hn
      · have hsign := J.radius_side j true z hz
        rw [hn] at hsign
        exact (not_le_of_gt (J.endpoint_sign j false) hsign).elim
    · cases b
      · have hsign := J.radius_side j false z hz
        rw [hp] at hsign
        exact (not_le_of_gt (J.endpoint_sign j true) hsign).elim
      · exact hp
  · rintro z rfl
    exact ⟨right_mem_segment ℝ _ _, J.endpoint_mem_rim j b⟩

theorem cross_radii (b c : Bool) : J.radius 0 c ∩ J.radius 1 b = {J.center} := by
  apply Subset.antisymm
  · exact fun z hz => J.axes_intersection.subset
      ⟨J.radius_subset_axis 0 c hz.1, J.radius_subset_axis 1 b hz.2⟩
  · rintro z rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

end SignedJointCross
end PoincareConjecture.M76.Dehn
