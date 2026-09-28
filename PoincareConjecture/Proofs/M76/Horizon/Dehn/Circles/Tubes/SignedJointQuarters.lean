import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.OriginalJointCross

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.SignedJointCross

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (J : SignedJointCross E)

theorem half_ball (j : Fin 2) (b : Bool) :
    IsFinitePLBallPair (ℝ × ℝ) (J.disk ∩ {z | side b (J.coordinate j z)})
      ((J.rim ∩ {z | side b (J.coordinate j z)}) ∪ J.axis j) := by
  have h := J.disk_ball.signed_halves_of_zero_arc (J.coordinate j)
    (J.coordinate_continuous j) (J.axis_ball j) (J.endpoints_ne j) rfl (J.rim_zero j)
    ⟨J.endpoint j.rev false, J.endpoint_mem_rim j.rev false, by
      simpa only [Fin.rev_rev, Bool.false_eq_true, if_false] using J.endpoint_sign j.rev false⟩
    ⟨J.endpoint j.rev true, J.endpoint_mem_rim j.rev true, by
      simpa only [Fin.rev_rev, if_true] using J.endpoint_sign j.rev true⟩
  cases b
  · exact h.1
  · simpa only [side, axis, if_true, union_comm] using h.2

theorem quarter_ball (b c : Bool) :
    IsFinitePLBallPair (ℝ × ℝ) (J.quarter b c)
      ((J.quarter b c ∩ J.rim) ∪ (J.radius 0 c ∪ J.radius 1 b)) := by
  let D := J.disk ∩ {z | side b (J.coordinate 0 z)}
  let rim := (J.rim ∩ {z | side b (J.coordinate 0 z)}) ∪ J.axis 0
  have hDzero : D ∩ {z | J.coordinate 1 z = 0} = J.radius 1 b := by
    rw [J.radius_cut]
    ext z
    exact ⟨fun hz => ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩,
      fun hz => ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩⟩
  have hrimzero : rim ∩ {z | J.coordinate 1 z = 0} = {J.center, J.endpoint 1 b} := by
    apply Subset.antisymm
    · rintro z ⟨hz | hz, hz1⟩
      · have hzR : z ∈ J.radius 1 b := (J.radius_cut 1 b).symm.subset
          ⟨⟨J.disk_ball.1 hz.1, hz1⟩, hz.2⟩
        exact Or.inr ((J.radius_rim 1 b).subset ⟨hzR, hz.1⟩)
      · exact Or.inl (J.axes_intersection.subset ⟨hz, hz.1, hz1⟩)
    · rintro z (rfl | rfl)
      · exact ⟨Or.inr (J.center_interior 0).1, J.center_zero 1⟩
      · have haR : J.endpoint 1 b ∈ J.radius 1 b := right_mem_segment ℝ _ _
        exact ⟨Or.inl ⟨J.endpoint_mem_rim 1 b, J.radius_side 1 b _ haR⟩,
          (J.radius_subset_axis 1 b haR).2⟩
  have h := (J.half_ball 0 b).signed_halves_of_zero_arc (J.coordinate 1)
    ((J.coordinate_continuous 1).mono inter_subset_left) (J.radius_ball 1 b)
    (J.endpoint_ne_center 1 b).symm hDzero hrimzero
    ⟨J.endpoint 0 false, Or.inr (J.radius_subset_axis 0 false (right_mem_segment ℝ _ _)),
      J.endpoint_sign 0 false⟩
    ⟨J.endpoint 0 true, Or.inr (J.radius_subset_axis 0 true (right_mem_segment ℝ _ _)),
      J.endpoint_sign 0 true⟩
  have hball : IsFinitePLBallPair (ℝ × ℝ) (D ∩ {z | side c (J.coordinate 1 z)})
      ((rim ∩ {z | side c (J.coordinate 1 z)}) ∪ J.radius 1 b) := by
    cases c
    · exact h.1
    · simpa only [D, rim, side, if_true, union_comm] using h.2
  have hcarrier : D ∩ {z | side c (J.coordinate 1 z)} = J.quarter b c := by
    ext z
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  have houter : (J.rim ∩ {z | side b (J.coordinate 0 z)}) ∩
      {z | side c (J.coordinate 1 z)} = J.quarter b c ∩ J.rim := by
    ext z
    exact ⟨fun h => ⟨⟨J.disk_ball.1 h.1.1, h.1.2, h.2⟩, h.1.1⟩,
      fun h => ⟨⟨h.2, h.1.2.1⟩, h.1.2.2⟩⟩
  have hboundary : (rim ∩ {z | side c (J.coordinate 1 z)}) ∪ J.radius 1 b =
      (J.quarter b c ∩ J.rim) ∪ (J.radius 0 c ∪ J.radius 1 b) := by
    have hr : J.radius 0 c = J.axis 0 ∩ {z | side c (J.coordinate 1 z)} := J.radius_cut 0 c
    change (((J.rim ∩ {z | side b (J.coordinate 0 z)}) ∪ J.axis 0) ∩
      {z | side c (J.coordinate 1 z)}) ∪ J.radius 1 b = _
    rw [union_inter_distrib_right, houter, ← hr, union_assoc]
  simpa only [hcarrier, hboundary] using hball

theorem quarter_axis_zero (b c : Bool) : J.quarter b c ∩ J.axis 0 = J.radius 0 c := by
  rw [J.radius_cut]
  ext z
  constructor
  · exact fun hz => ⟨hz.2, hz.1.2.2⟩
  · intro hz
    refine ⟨⟨hz.1.1, ?_, hz.2⟩, hz.1⟩
    have hz0 : J.coordinate 0 z = 0 := hz.1.2
    cases b <;> simp [side, hz0]

theorem quarter_axis_one (b c : Bool) : J.quarter b c ∩ J.axis 1 = J.radius 1 b := by
  rw [J.radius_cut]
  ext z
  constructor
  · exact fun hz => ⟨hz.2, hz.1.2.1⟩
  · intro hz
    refine ⟨⟨hz.1.1, hz.2, ?_⟩, hz.1⟩
    have hz1 : J.coordinate 1 z = 0 := hz.1.2
    cases c <;> simp [side, hz1]

theorem quarter_boundary_arcs (b c : Bool) :
    IsFinitePLBallPair ℝ (J.radius 0 c ∪ J.radius 1 b) {J.endpoint 0 c, J.endpoint 1 b} ∧
    IsFinitePLBallPair ℝ (J.quarter b c ∩ J.rim) {J.endpoint 0 c, J.endpoint 1 b} ∧
    (J.radius 0 c ∪ J.radius 1 b) ∩ (J.quarter b c ∩ J.rim) =
      {J.endpoint 0 c, J.endpoint 1 b} := by
  let U := J.radius 0 c ∪ J.radius 1 b
  let O := J.quarter b c ∩ J.rim
  have hR0 : J.radius 0 c ⊆ J.quarter b c :=
    fun _ hz => ((J.quarter_axis_zero b c).symm.subset hz).1
  have hR1 : J.radius 1 b ⊆ J.quarter b c :=
    fun _ hz => ((J.quarter_axis_one b c).symm.subset hz).1
  have hU : IsFinitePLBallPair ℝ U {J.endpoint 0 c, J.endpoint 1 b} := by
    have hinter : segment ℝ (J.endpoint 0 c) J.center ∩
        segment ℝ J.center (J.endpoint 1 b) = {J.center} := by
      simpa only [radius, segment_symm (𝕜 := ℝ) (J.endpoint 0 c) J.center]
        using J.cross_radii b c
    have h := isFinitePLBallPair_two_segments (J.endpoint_ne_center 0 c)
      (J.endpoint_ne_center 1 b).symm hinter
    simpa only [U, radius, segment_symm (𝕜 := ℝ) (J.endpoint 0 c) J.center] using h
  have hends : J.endpoint 0 c ≠ J.endpoint 1 b := by
    intro h
    exact J.endpoint_ne_center 0 c ((J.cross_radii b c).subset
      ⟨right_mem_segment ℝ _ _, h.symm ▸ right_mem_segment ℝ _ _⟩)
  have hUO : U ∩ O = {J.endpoint 0 c, J.endpoint 1 b} := by
    apply Subset.antisymm
    · rintro z ⟨hz | hz, _, hzq⟩
      · exact Or.inl ((J.radius_rim 0 c).subset ⟨hz, hzq⟩)
      · exact Or.inr ((J.radius_rim 1 b).subset ⟨hz, hzq⟩)
    · rintro z (rfl | rfl)
      · exact ⟨Or.inl (right_mem_segment ℝ _ _), hR0 (right_mem_segment ℝ _ _),
          J.endpoint_mem_rim 0 c⟩
      · exact ⟨Or.inr (right_mem_segment ℝ _ _), hR1 (right_mem_segment ℝ _ _),
          J.endpoint_mem_rim 1 b⟩
  obtain ⟨O', hO', hwhole, hinter⟩ := (J.quarter_ball b c).exists_boundary_arc_complement
    hU subset_union_right hends
  have hOeq : O' = O := by
    apply Subset.antisymm
    · intro z hz
      by_cases hzU : z ∈ U
      · exact (hUO.symm.subset (hinter.subset ⟨hzU, hz⟩)).2
      · exact (hwhole.subset (Or.inr hz)).resolve_right hzU
    · intro z hz
      by_cases hzU : z ∈ U
      · exact hO'.1 (hUO.subset ⟨hzU, hz⟩)
      · exact (hwhole.symm.subset (Or.inl hz)).resolve_left hzU
  have hOball : IsFinitePLBallPair ℝ O {J.endpoint 0 c, J.endpoint 1 b} := by
    rw [← hOeq]
    exact hO'
  exact ⟨hU, hOball, hUO⟩

theorem quarter_intersections (b c : Bool) :
    J.quarter b c ∩ J.quarter b (!c) = J.radius 1 b ∧
    J.quarter b c ∩ J.quarter (!b) c = J.radius 0 c ∧
    J.quarter b c ∩ J.quarter (!b) (!c) = {J.center} := by
  have hboth (b : Bool) {x : ℝ} (h : side b x) (h' : side (!b) x) : x = 0 := by
    cases b
    · exact le_antisymm h h'
    · exact le_antisymm h' h
  have hm (b c : Bool) : J.center ∈ J.quarter b c := by
    refine ⟨(J.center_interior 0).1.1, ?_, ?_⟩
    · cases b <;> simp [side, J.center_zero]
    · cases c <;> simp [side, J.center_zero]
  refine ⟨?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro z hz
      exact (J.quarter_axis_one b c).subset
        ⟨hz.1, hz.1.1, hboth c hz.1.2.2 hz.2.2.2⟩
    · intro z hz
      exact ⟨((J.quarter_axis_one b c).symm.subset hz).1,
        ((J.quarter_axis_one b (!c)).symm.subset hz).1⟩
  · apply Subset.antisymm
    · intro z hz
      exact (J.quarter_axis_zero b c).subset
        ⟨hz.1, hz.1.1, hboth b hz.1.2.1 hz.2.2.1⟩
    · intro z hz
      exact ⟨((J.quarter_axis_zero b c).symm.subset hz).1,
        ((J.quarter_axis_zero (!b) c).symm.subset hz).1⟩
  · apply Subset.antisymm
    · intro z hz
      exact J.axes_intersection.subset
        ⟨⟨hz.1.1, hboth b hz.1.2.1 hz.2.2.1⟩, hz.1.1, hboth c hz.1.2.2 hz.2.2.2⟩
    · rintro z rfl
      exact ⟨hm b c, hm (!b) (!c)⟩

omit [FiniteDimensional ℝ E] in
theorem quarter_union : (⋃ b : Bool, ⋃ c : Bool, J.quarter b c) = J.disk := by
  ext z
  constructor
  · intro hz
    obtain ⟨b, c, hz⟩ := mem_iUnion₂.mp hz
    exact hz.1
  · intro hz
    have hside (x : ℝ) : ∃ b : Bool, side b x := by
      rcases le_total x 0 with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨b, hb⟩ := hside (J.coordinate 0 z)
    obtain ⟨c, hc⟩ := hside (J.coordinate 1 z)
    exact mem_iUnion₂.mpr ⟨b, c, hz, hb, hc⟩

end PoincareConjecture.M76.Dehn.SignedJointCross
