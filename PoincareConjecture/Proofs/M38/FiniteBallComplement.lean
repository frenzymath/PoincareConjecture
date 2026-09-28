import PoincareConjecture.Proofs.M38.SurgeryBallNeighborhood
import PoincareConjecture.Proofs.M38.CapAnnulus

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem preconnected_diff_closed_of_local
    {X : Type*} [TopologicalSpace X] {C K W : Set X}
    (hC : IsPreconnected C) (hK : IsClosed K) (hne : K.Nonempty)
    (hW : IsOpen W) (hKW : K ⊆ W) (hWC : W ⊆ C)
    (houter : IsPreconnected (W \ K)) : IsPreconnected (C \ K) := by
  apply isPreconnected_iff_subset_of_disjoint.mpr
  intro a b ha hb hcover hdisjoint
  have hlocalcover : W \ K ⊆ a ∪ b := fun _ hx => hcover ⟨hWC hx.1, hx.2⟩
  have hlocaldisjoint : (W \ K) ∩ (a ∩ b) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hy, hab⟩
    have hbad : y ∈ (C \ K) ∩ (a ∩ b) := ⟨⟨hWC hy.1, hy.2⟩, hab⟩
    simp only [hdisjoint, mem_empty_iff_false] at hbad
  have hside (a b : Set X) (ha : IsOpen a) (hb : IsOpen b)
      (hcover : C \ K ⊆ a ∪ b) (hdisjoint : (C \ K) ∩ (a ∩ b) = ∅)
      (hWa : W \ K ⊆ a) : C \ K ⊆ a := by
    have hfullcover : C ⊆ (a ∪ W) ∪ (b \ K) := by
      intro y hy
      by_cases hyK : y ∈ K
      · exact Or.inl (Or.inr (hKW hyK))
      · rcases hcover ⟨hy, hyK⟩ with hya | hyb
        · exact Or.inl (Or.inl hya)
        · exact Or.inr ⟨hyb, hyK⟩
    have hfulldisjoint : C ∩ ((a ∪ W) ∩ (b \ K)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hyC, hya, hyb, hyK⟩
      have hya' : y ∈ a := hya.elim id (fun hyW => hWa ⟨hyW, hyK⟩)
      have hbad : y ∈ (C \ K) ∩ (a ∩ b) := ⟨⟨hyC, hyK⟩, hya', hyb⟩
      simp only [hdisjoint, mem_empty_iff_false] at hbad
    rcases isPreconnected_iff_subset_of_disjoint.mp hC (a ∪ W) (b \ K)
        (ha.union hW) (hb.inter hK.isOpen_compl) hfullcover hfulldisjoint with hall | hall
    · intro y hy
      exact (hall hy.1).elim id (fun hyW => hWa ⟨hyW, hy.2⟩)
    · obtain ⟨y, hy⟩ := hne
      exact ((hall (hWC (hKW hy))).2 hy).elim
  rcases isPreconnected_iff_subset_of_disjoint.mp houter a b ha hb
      hlocalcover hlocaldisjoint with hlocal | hlocal
  · exact Or.inl (hside a b ha hb hcover hdisjoint hlocal)
  · exact Or.inr (hside b a hb ha (by rwa [union_comm])
      (by rw [inter_comm b a]; exact hdisjoint) hlocal)

theorem surgeryBall_outer_annulus_connected
    {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A) :
    IsConnected ((B.map '' Metric.ball 0 2) \ B.closedBall) := by
  let f : RoundCylinderSpace → A.carrier := B.map ∘ capAttachVector
  have hconnected : IsConnected ((univ : Set UnitTwoSphere) ×ˢ Ioo (0 : ℝ) 1) := by
    let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
    exact isConnected_univ.prod (isConnected_Ioo zero_lt_one)
  have hf : ContinuousOn f (univ ×ˢ Ioo (0 : ℝ) 1) := by
    apply B.map_smooth.continuousOn.comp capAttachVector_smooth.continuous.continuousOn
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right] using (capAttachVector_mem hz).2
  have himage : f '' (univ ×ˢ Ioo (0 : ℝ) 1) =
      (B.map '' Metric.ball 0 2) \ B.closedBall := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      have hn := capAttachVector_mem hz
      have hz2 : capAttachVector z ∈ Metric.ball (0 : StandardCapSpace) 2 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hn.2
      refine ⟨⟨capAttachVector z, hz2, rfl⟩, ?_⟩
      intro hball
      have hle := (surgeryBall_mem_closedBall_iff B ⟨capAttachVector z, hz2, rfl⟩).mp hball
      rw [B.left_inverse hz2] at hle
      exact hn.1.not_ge hle
    · rintro y ⟨⟨z, hz, rfl⟩, hy⟩
      have hn : 1 < ‖z‖ := by
        apply lt_of_not_ge
        intro hle
        exact hy ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hle, rfl⟩
      have hn2 : ‖z‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      exact ⟨capAttachCoordinates z, capAttachCoordinates_mem ⟨hn, hn2⟩,
        congrArg B.map (capAttachVector_coordinates z)⟩
  rw [← himage]
  exact hconnected.image f hf

theorem finite_surgeryBall_complement_preconnected
    {A : GeneralizedSliceCarrier.{u}} (hA : IsPreconnected (univ : Set A.carrier))
    {ι : Type*} (B : ι → SurgeryBallEmbedding A)
    (hB : ∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall)
    (s : Finset ι) : IsPreconnected (⋃ i ∈ s, (B i).closedBall)ᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, compl_empty] using hA
  | @insert i s hi ih =>
      let U : Set A.carrier := (⋃ j ∈ s, (B j).closedBall)ᶜ
      have hU : IsOpen U := (s.finite_toSet.isClosed_biUnion
        (fun j _ => (surgeryBall_closedImage_compact (B j) 1 (by norm_num)).isClosed)).isOpen_compl
      have hBU : (B i).closedBall ⊆ U := by
        intro y hy hunion
        obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hunion
        exact disjoint_left.mp (hB i j (fun h => hi (h ▸ hj))) hy hyj
      obtain ⟨D, hD, _, hDU⟩ := exists_surgeryBall_with_image_in_open (B i) hU hBU
      have h := preconnected_diff_closed_of_local ih
        (surgeryBall_closedImage_compact D 1 (by norm_num)).isClosed
        (surgeryBall_closedBall_connected D).nonempty
        (surgeryBall_image_open D) (surgeryBall_closedBall_subset_image D)
        hDU (surgeryBall_outer_annulus_connected D).isPreconnected
      have hset : U \ D.closedBall = (⋃ j ∈ insert i s, (B j).closedBall)ᶜ := by
        rw [hD, Finset.set_biUnion_insert, compl_union, inter_comm]
        rfl
      change IsPreconnected (U \ D.closedBall) at h
      rwa [hset] at h

theorem surgeryBall_iUnion_complement_connected
    {A : GeneralizedSliceCarrier.{u}} (hA : IsPreconnected (univ : Set A.carrier))
    {ι : Type*} [Finite ι] (B : ι → SurgeryBallEmbedding A)
    (hB : ∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall)
    (p : A.carrier) (hp : ∀ i, p ∉ (B i).closedBall) :
    IsConnected (⋃ i, (B i).closedBall)ᶜ := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨⟨p, ?_⟩, ?_⟩
  · simpa only [mem_compl_iff, mem_iUnion, not_exists] using hp
  · simpa only [Finset.mem_univ, iUnion_true] using
      finite_surgeryBall_complement_preconnected hA B hB Finset.univ

end PoincareConjecture.M38
