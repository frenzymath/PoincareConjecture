import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall











set_option autoImplicit false

open Set Geometry

namespace CoordinateHalfBoxes



def base (r : ℝ) : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Icc (-r) r



def baseBoundary (r : ℝ) : Set (ℝ × ℝ) :=
  ({-r, r} ×ˢ Icc (-r) r) ∪ (Icc (-r) r ×ˢ {-r, r})



def box (r : ℝ) : Set ((ℝ × ℝ) × ℝ) := base r ×ˢ Icc (-r) r



def boxBoundary (r : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  (baseBoundary r ×ˢ Icc (-r) r) ∪ (base r ×ˢ {-r, r})



def upper (r : ℝ) : Set ((ℝ × ℝ) × ℝ) := base r ×ˢ Icc 0 r



def lower (r : ℝ) : Set ((ℝ × ℝ) × ℝ) := base r ×ˢ Icc (-r) 0



def disk (r : ℝ) : Set ((ℝ × ℝ) × ℝ) := base r ×ˢ {0}



def rim (r : ℝ) : Set ((ℝ × ℝ) × ℝ) := baseBoundary r ×ˢ {0}



def upperOuter (r : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  (baseBoundary r ×ˢ Icc 0 r) ∪ (base r ×ˢ {r})



def lowerOuter (r : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  (baseBoundary r ×ˢ Icc (-r) 0) ∪ (base r ×ˢ {-r})



theorem base_ballPair {r : ℝ} (hr : 0 < r) :
    IsFinitePLBallPair (ℝ × ℝ) (base r) (baseBoundary r) :=
  (isFinitePLBallPair_Icc (show -r < r by linarith)).prod
    (isFinitePLBallPair_Icc (show -r < r by linarith))



theorem box_ballPair {r : ℝ} (hr : 0 < r) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (box r) (boxBoundary r) :=
  (base_ballPair hr).prod (isFinitePLBallPair_Icc (show -r < r by linarith))



theorem upper_ballPair {r : ℝ} (hr : 0 < r) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (upper r) (disk r ∪ upperOuter r) := by
  have h := (base_ballPair hr).prod (isFinitePLBallPair_Icc hr)
  have hb : (baseBoundary r ×ˢ Icc 0 r) ∪ (base r ×ˢ {0, r}) =
      disk r ∪ upperOuter r := by
    ext p
    simp only [disk, upperOuter, mem_prod, mem_union, mem_insert_iff, mem_singleton_iff]
    tauto
  rwa [hb] at h



theorem lower_ballPair {r : ℝ} (hr : 0 < r) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (lower r) (disk r ∪ lowerOuter r) := by
  have h := (base_ballPair hr).prod
    (isFinitePLBallPair_Icc (show -r < 0 by linarith))
  have hb : (baseBoundary r ×ˢ Icc (-r) 0) ∪ (base r ×ˢ {-r, 0}) =
      disk r ∪ lowerOuter r := by
    ext p
    simp only [disk, lowerOuter, mem_prod, mem_union, mem_insert_iff, mem_singleton_iff]
    tauto
  rwa [hb] at h



theorem disk_ballPair {r : ℝ} (hr : 0 < r) :
    IsFinitePLBallPair (ℝ × ℝ) (disk r) (rim r) :=
  (base_ballPair hr).prod_singleton 0



theorem upper_union_lower {r : ℝ} (hr : 0 ≤ r) : upper r ∪ lower r = box r := by
  ext p
  change ((p.1 ∈ base r ∧ p.2 ∈ Icc 0 r) ∨
    (p.1 ∈ base r ∧ p.2 ∈ Icc (-r) 0)) ↔
      p.1 ∈ base r ∧ p.2 ∈ Icc (-r) r
  constructor
  · rintro (⟨hp, ht⟩ | ⟨hp, ht⟩)
    · exact ⟨hp, by linarith [ht.1], ht.2⟩
    · exact ⟨hp, ht.1, by linarith [ht.2]⟩
  · rintro ⟨hp, ht⟩
    rcases le_total 0 p.2 with h | h
    · exact Or.inl ⟨hp, h, ht.2⟩
    · exact Or.inr ⟨hp, ht.1, h⟩



theorem upper_inter_lower {r : ℝ} (hr : 0 ≤ r) : upper r ∩ lower r = disk r := by
  ext p
  change ((p.1 ∈ base r ∧ p.2 ∈ Icc 0 r) ∧
    (p.1 ∈ base r ∧ p.2 ∈ Icc (-r) 0)) ↔ p.1 ∈ base r ∧ p.2 = 0
  constructor
  · rintro ⟨⟨hp, ht⟩, ⟨_, hu⟩⟩
    exact ⟨hp, le_antisymm hu.2 ht.1⟩
  · rintro ⟨hp, ht⟩
    rw [ht]
    exact ⟨⟨hp, le_rfl, hr⟩, hp, neg_nonpos.mpr hr, le_rfl⟩



theorem box_inter_plane {r : ℝ} (hr : 0 ≤ r) :
    box r ∩ {p | p.2 = 0} = disk r := by
  ext p
  change ((p.1 ∈ base r ∧ p.2 ∈ Icc (-r) r) ∧ p.2 = 0) ↔
    p.1 ∈ base r ∧ p.2 = 0
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hp, ht⟩
    rw [ht]
    exact ⟨⟨hp, neg_nonpos.mpr hr, hr⟩, rfl⟩



theorem box_eq_closedBall (r : ℝ) : box r = Metric.closedBall 0 r := by
  ext p
  simp only [box, base, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right,
    Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]



theorem zero_mem_interior_box {r : ℝ} (hr : 0 < r) :
    (0 : (ℝ × ℝ) × ℝ) ∈ interior (box r) := by
  rw [box_eq_closedBall]
  exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)



theorem exists_box_subset {U : Set ((ℝ × ℝ) × ℝ)} (hU : IsOpen U)
    (hzero : (0 : (ℝ × ℝ) × ℝ) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ box r ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  rw [box_eq_closedBall]
  exact (Metric.closedBall_subset_ball (by linarith)).trans hεU

end CoordinateHalfBoxes
