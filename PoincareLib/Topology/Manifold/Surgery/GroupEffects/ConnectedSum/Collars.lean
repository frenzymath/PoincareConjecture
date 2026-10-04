import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Coordinates

/-! Adapted from Mapher `PoincareMT/Proofs/M54/ConnectedSum/Collars.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# The open covers of a connected sum

The punctured first side and the second side enlarged by the collar form
an open cover whose overlap is the negative collar. Reversing the roles
gives the positive collar. These are the covers for van Kampen in
Morgan--Tian Proposition 15.3 (pp. 357-358).
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.SmoothConnectedSumData

variable {A B C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)

/-- The image of a displayed open band in the neck coordinates of
MT Proposition 15.3 (pp. 357-358). -/
def collarBand (a b : ℝ) : Set C.carrier := S.collar '' (univ ×ˢ Ioo a b)

/-- A nonempty subinterval of the neck gives a simply connected band
(MT Proposition 15.3, pp. 357-358). -/
theorem collarBand_simplyConnected (a b : ℝ) (hab : a < b)
    (ha : -1 ≤ a) (hb : b ≤ 1) : IsSimplyConnected (S.collarBand a b) := by
  have hsub : (univ ×ˢ Ioo a b : Set RoundCylinderSpace) ⊆ univ ×ˢ Ioo (-1 : ℝ) 1 :=
    fun _ hz => ⟨hz.1, lt_of_le_of_lt ha hz.2.1, lt_of_lt_of_le hz.2.2 hb⟩
  let e : (univ ×ˢ Ioo a b : Set RoundCylinderSpace) ≃ₜ S.collarBand a b :=
    Homeomorph.ofSetInverse S.collar S.collar_inverse _ _
      (S.collar_smooth.continuousOn.mono hsub)
      (S.collar_inverse_smooth.continuousOn.mono (image_mono hsub))
      (fun _ hz => mem_image_of_mem _ hz)
      (by rintro _ ⟨z, hz, rfl⟩; simpa only [S.collar_left_inverse (hsub hz)] using hz)
      (fun _ hz => S.collar_left_inverse (hsub hz))
      (fun _ hy => S.collar_right_inverse (image_mono hsub hy))
  let : SimplyConnectedSpace (univ ×ˢ Ioo a b : Set RoundCylinderSpace) :=
    SurgeryCoordinates.cylinder_interval_simplyConnected a b hab
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- Negative collar points lie in the punctured first side, as specified
by the ball coordinates in MT Proposition 15.3, pp. 357-358. -/
theorem negative_mem_first (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 0) :
    S.collar (z, s) ∈ S.first_region := by
  rw [S.negative_gluing z s hs]
  apply S.first_identify.map_image.subset
  exact mem_image_of_mem _ (S.first_ball.radial_mem_complement z (by
    constructor <;> linarith [hs.1, hs.2]))

/-- Positive collar points lie in the punctured second side, including
the sphere gluing map of MT Proposition 15.3, pp. 357-358. -/
theorem positive_mem_second (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    S.collar (z, s) ∈ S.second_region := by
  rw [S.positive_gluing z s hs]
  apply S.second_identify.map_image.subset
  exact mem_image_of_mem _ (S.second_ball.radial_mem_complement (S.sphere_gluing z) (by
    constructor <;> linarith [hs.1, hs.2]))

/-- The central sphere meets neither punctured region in the frozen
connected-sum model (MT Proposition 15.3, pp. 357-358). -/
theorem central_not_mem (z : UnitTwoSphere) :
    S.collar (z, 0) ∉ S.first_region ∪ S.second_region := by
  exact fun h => Set.disjoint_left.mp S.central_disjoint
    (mem_image_of_mem S.collar ⟨mem_univ z, mem_singleton 0⟩) h

/-- The first punctured side and the second side with the full collar
cover the connected sum (MT Proposition 15.3, pp. 357-358). -/
theorem first_cover : S.first_region ∪ (S.second_region ∪ S.collarBand (-1) 1) = univ := by
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ S.first_region ∪ S.second_region ∪
      S.collar '' (univ ×ˢ ({0} : Set ℝ)) := S.cover.symm ▸ mem_univ x
  rcases hx with (h | h) | ⟨⟨z, s⟩, hs, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have hs0 : s = 0 := hs.2
    subst s
    exact Or.inr (Or.inr (mem_image_of_mem _ ⟨mem_univ z, by constructor <;> norm_num⟩))

/-- The overlap for the first-side van Kampen cover is exactly the
negative collar (MT Proposition 15.3, pp. 357-358). -/
theorem first_overlap :
    S.first_region ∩ (S.second_region ∪ S.collarBand (-1) 1) = S.collarBand (-1) 0 := by
  ext x
  constructor
  · rintro ⟨hx, hy | ⟨⟨z, s⟩, hs, rfl⟩⟩
    · exact False.elim (Set.disjoint_left.mp S.regions_disjoint hx hy)
    · have hs0 : s < 0 := by
        rcases lt_trichotomy s 0 with h | h | h
        · exact h
        · subst s; exact False.elim (S.central_not_mem z (Or.inl hx))
        · exact False.elim (Set.disjoint_left.mp S.regions_disjoint hx
            (S.positive_mem_second z ⟨h, hs.2.2⟩))
      exact mem_image_of_mem _ ⟨mem_univ z, hs.2.1, hs0⟩
  · rintro ⟨⟨z, s⟩, hs, rfl⟩
    exact ⟨S.negative_mem_first z hs.2, Or.inr (mem_image_of_mem _
      ⟨mem_univ z, hs.2.1, lt_trans hs.2.2 zero_lt_one⟩)⟩

/-- The reversed van Kampen cover also covers the connected sum
(MT Proposition 15.3, pp. 357-358). -/
theorem second_cover : S.second_region ∪ (S.first_region ∪ S.collarBand (-1) 1) = univ := by
  rw [← union_assoc, union_comm S.second_region S.first_region, union_assoc, S.first_cover]

/-- The reversed overlap is the positive collar, with the central sphere
excluded (MT Proposition 15.3, pp. 357-358). -/
theorem second_overlap :
    S.second_region ∩ (S.first_region ∪ S.collarBand (-1) 1) = S.collarBand 0 1 := by
  ext x
  constructor
  · rintro ⟨hx, hy | ⟨⟨z, s⟩, hs, rfl⟩⟩
    · exact False.elim (Set.disjoint_left.mp S.regions_disjoint hy hx)
    · have hs0 : 0 < s := by
        rcases lt_trichotomy s 0 with h | h | h
        · exact False.elim (Set.disjoint_left.mp S.regions_disjoint
            (S.negative_mem_first z ⟨hs.2.1, h⟩) hx)
        · subst s; exact False.elim (S.central_not_mem z (Or.inr hx))
        · exact h
      exact mem_image_of_mem _ ⟨mem_univ z, hs0, hs.2.2⟩
  · rintro ⟨⟨z, s⟩, hs, rfl⟩
    exact ⟨S.positive_mem_second z hs.2, Or.inr (mem_image_of_mem _
      ⟨mem_univ z, lt_trans (by norm_num : (-1 : ℝ) < 0) hs.2.1, hs.2.2⟩)⟩

end PoincareMT.SmoothConnectedSumData
