import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoStandardFrame









set_option autoImplicit false

open Set Metric Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.HamiltonIndexTwoStandard

local notation "P" => ((ℝ × ℝ) × ℝ)
local notation "V" => (Fin 3 → ℝ)


def middle : Set V := coordinates '' prism (-(3 / 2)) (3 / 2)


def disk (j : Bool) : Set V := coordinates '' endDisk (endHeight j)

private theorem base_boundary_subset : baseBoundary 1 ⊆ base 1 :=
  (base_ballPair (by norm_num : (0 : ℝ) < 1)).1

private theorem endDisk_inter_band {a b t : ℝ} (ht : t ∈ Icc a b) :
    endDisk t ∩ band a b = endRim t := by
  ext p
  constructor
  · rintro ⟨hd, hb⟩
    exact ⟨hb.1, hd.2⟩
  · intro hq
    refine ⟨⟨base_boundary_subset hq.1, hq.2⟩, hq.1, ?_⟩
    rwa [show p.2 = t from hq.2]

private theorem endDisk_inter_outer (j : Bool) :
    endDisk (endHeight j) ∩
      (if j then upperOuter (3 / 2) 2 else lowerOuter (-2) (-(3 / 2))) =
        endRim (endHeight j) := by
  cases j <;> simp only [endHeight, Bool.false_eq_true, if_false, if_true]
  all_goals
    ext p
    constructor
    · rintro ⟨hd, ho⟩
      rcases ho with hb | ho
      · exact ⟨hb.1, hd.2⟩
      · have ht := hd.2
        have hu := ho.2
        change p.2 = _ at ht hu
        norm_num at ht hu
        linarith
    · intro hq
      refine ⟨⟨base_boundary_subset hq.1, hq.2⟩, Or.inl ⟨hq.1, ?_⟩⟩
      change _ ≤ p.2 ∧ p.2 ≤ _
      have ht := hq.2
      change p.2 = _ at ht
      rw [ht]
      norm_num

private theorem middle_boundary_inter_outer (j : Bool) :
    ((band (-(3 / 2)) (3 / 2) ∪ endDisk (-(3 / 2))) ∪ endDisk (3 / 2)) ∩
      (if j then upperOuter (3 / 2) 2 else lowerOuter (-2) (-(3 / 2))) =
        endRim (endHeight j) := by
  have hmiddle := (prism_ballPair
    (by norm_num : -(3 / 2 : ℝ) < 3 / 2)).1
  apply Subset.antisymm
  · intro p hp
    have hprism := hmiddle hp.1
    have ht : p.2 = endHeight j := by
      cases j with
      | false =>
          change p.2 = -(3 / 2)
          rcases hp.2 with hb | he
          · exact le_antisymm hb.2.2 hprism.2.1
          · have he' : p.2 = -2 := he.2
            linarith [hprism.2.1]
      | true =>
          change p.2 = 3 / 2
          rcases hp.2 with hb | he
          · exact le_antisymm hprism.2.2 hb.2.1
          · have he' : p.2 = 2 := he.2
            linarith [hprism.2.2]
    exact (endDisk_inter_outer j).subset ⟨⟨hprism.1, ht⟩, hp.2⟩
  · intro p hp
    have hd := (endDisk_ballPair (endHeight j)).1 hp
    refine ⟨?_, ((endDisk_inter_outer j).symm.subset hp).2⟩
    cases j with
    | false => exact Or.inl (Or.inr hd)
    | true => exact Or.inr hd




noncomputable def source : HamiltonIndexTwoMarkedBall frame := by
  refine {
    carrier := middle
    disk := disk
    ball := ?_
    subset_box := ?_
    diskBall := ?_
    disk_outer := ?_
    disk_side := ?_
    disksDisjoint := ?_
    boundary_outer := ?_
  }
  · change IsFinitePLBallPair P middle ((side ∪ disk false) ∪ disk true)
    have h := (prism_ballPair
      (by norm_num : -(3 / 2 : ℝ) < 3 / 2)).affine_image
      coordinates.toContinuousAffineMap coordinates.injective.injOn
    change IsFinitePLBallPair P (coordinates '' prism (-(3 / 2)) (3 / 2))
      (coordinates '' ((band (-(3 / 2)) (3 / 2) ∪ endDisk (-(3 / 2))) ∪
        endDisk (3 / 2))) at h
    simpa only [image_union, middle, side, disk, endHeight,
      Bool.false_eq_true, if_false, if_true] using h
  · change middle ⊆ Icc lowerBound upperBound
    rw [← box_image]
    apply image_mono
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  · intro j
    exact (endDisk_ballPair (endHeight j)).affine_image
      coordinates.toContinuousAffineMap coordinates.injective.injOn
  · intro j
    change (coordinates '' endDisk (endHeight j)) ∩
      (coordinates '' (if j then upperOuter (3 / 2) 2 else
        lowerOuter (-2) (-(3 / 2)))) = coordinates '' endRim (endHeight j)
    rw [← image_inter coordinates.injective, endDisk_inter_outer]
  · intro j
    change (coordinates '' endDisk (endHeight j)) ∩
      (coordinates '' band (-(3 / 2)) (3 / 2)) = coordinates '' endRim (endHeight j)
    rw [← image_inter coordinates.injective, endDisk_inter_band]
    cases j <;> norm_num [endHeight]
  · apply Set.disjoint_left.mpr
    rintro x ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
    have hqp : q = p := coordinates.injective heq
    subst q
    have hlo : p.2 = -(3 / 2) := hp.2
    have hhi : p.2 = 3 / 2 := hq.2
    linarith
  · intro j
    change (((coordinates '' band (-(3 / 2)) (3 / 2)) ∪
      (coordinates '' endDisk (-(3 / 2)))) ∪ (coordinates '' endDisk (3 / 2))) ∩
        (coordinates '' (if j then upperOuter (3 / 2) 2 else
          lowerOuter (-2) (-(3 / 2)))) = coordinates '' endRim (endHeight j)
    rw [← image_union, ← image_union, ← image_inter coordinates.injective,
      middle_boundary_inter_outer]



theorem unit_core_subset_source : closedBall (0 : V) 1 ⊆ source.carrier := by
  intro x hx
  have hn : ∀ i, |x i| ≤ 1 := by
    have h := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
      (mem_closedBall_zero_iff.mp hx)
    simpa only [Real.norm_eq_abs] using h
  refine ⟨((x 0, x 1), x 2), ?_, ?_⟩
  · exact ⟨⟨abs_le.mp (hn 0), abs_le.mp (hn 1)⟩,
      by linarith [(abs_le.mp (hn 2)).1], by linarith [(abs_le.mp (hn 2)).2]⟩
  · ext i
    fin_cases i <;> rfl

end PoincareConjecture.M76.HamiltonIndexTwoStandard
