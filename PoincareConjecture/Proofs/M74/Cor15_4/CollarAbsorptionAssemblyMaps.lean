import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionOuterChart

set_option autoImplicit false

open Set Metric EuclideanGeometry
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M74.CollarEndChartData

variable {Y : GeneralizedSliceCarrier.{u}} (D : CollarEndChartData Y)

def assembledSource : Set Y.carrier := {D.second.symm 0}ᶜ

noncomputable def assembledMap (x : Y.carrier) : StandardCapSpace := by
  classical
  exact if x ∈ D.first.source then collarBallMap (D.first x)
    else if x ∈ D.second.source then collarOuterMap (D.second x)
    else collarRadialMap (D.neck.symm x)

noncomputable def assembledInverse (q0 : UnitTwoSphere) (z : StandardCapSpace) : Y.carrier := by
  classical
  exact if ‖z‖ < 2 then D.first.symm (collarBallInverse z)
    else if 2 < ‖z‖ then D.second.symm (collarOuterInverse z)
    else D.neck (collarRadialInverse q0 z)

theorem assembledMap_first {x : Y.carrier} (hx : x ∈ D.first.source) :
    D.assembledMap x = collarBallMap (D.first x) := by
  simp only [assembledMap, if_pos hx]

theorem assembledMap_second {x : Y.carrier} (hx : x ∈ D.second.source) :
    D.assembledMap x = collarOuterMap (D.second x) := by
  have hn : x ∉ D.first.source := fun h => disjoint_left.mp D.disjoint h hx
  simp only [assembledMap, if_neg hn, if_pos hx]

theorem assembledMap_central (q : UnitTwoSphere) :
    D.assembledMap (D.neck (q, 0)) = collarRadialMap (q, 0) := by
  have hn₁ : D.neck (q, 0) ∉ D.first.source :=
    fun h => D.central_disjoint q (Or.inl h)
  have hn₂ : D.neck (q, 0) ∉ D.second.source :=
    fun h => D.central_disjoint q (Or.inr h)
  rw [assembledMap, if_neg hn₁, if_neg hn₂, D.neck.left_inv (D.central_mem_source q)]

theorem assembledMap_neck {p : RoundCylinderSpace} (hp : p ∈ D.neck.source) :
    D.assembledMap (D.neck p) = collarRadialMap p := by
  rcases p with ⟨q, s⟩
  rw [D.neck_source] at hp
  rcases lt_trichotomy s 0 with hs | hs | hs
  · rw [D.assembledMap_first (D.negative_mem q s ⟨hp.2.1, hs⟩),
      D.negative_eq q s ⟨hp.2.1, hs⟩, collarBallMap_negative_end q hs]
  · subst s
    exact D.assembledMap_central q
  · rw [D.assembledMap_second (D.positive_mem q s ⟨hs, hp.2.2⟩),
      D.positive_eq q s ⟨hs, hp.2.2⟩]
    exact collarBallMap_positive_end q hs

theorem assembledMap_secondCenter : D.assembledMap (D.second.symm 0) = 0 := by
  rw [D.assembledMap_second (D.second.map_target (D.mem_second_target 0)),
    D.second.right_inv (D.mem_second_target 0), collarOuterMap_zero]

theorem neck_mem_assembledSource {p : RoundCylinderSpace} (hp : p ∈ D.neck.source) :
    D.neck p ∈ D.assembledSource := by
  intro heq
  apply collarRadialMap_ne_zero p
  rw [← D.assembledMap_neck hp, heq, D.assembledMap_secondCenter]

theorem first_mem_assembledSource {x : Y.carrier} (hx : x ∈ D.first.source) :
    x ∈ D.assembledSource := by
  intro heq
  rw [heq] at hx
  exact disjoint_left.mp D.disjoint hx (D.second.map_target (D.mem_second_target 0))

theorem second_eq_zero_iff {x : Y.carrier} (hx : x ∈ D.second.source) :
    D.second x = 0 ↔ x = D.second.symm 0 := by
  constructor
  · intro h
    have heq := D.second.left_inv hx
    rw [h] at heq
    exact heq.symm
  · rintro rfl
    exact D.second.right_inv (D.mem_second_target 0)

theorem assembledInverse_map (q0 : UnitTwoSphere) {x : Y.carrier}
    (hx : x ∈ D.assembledSource) : D.assembledInverse q0 (D.assembledMap x) = x := by
  rcases D.cover_cases x with hx₁ | hx₂ | ⟨q, rfl⟩
  · have hn := mem_ball_zero_iff.mp (collarBallMap_mem (D.first x))
    rw [D.assembledMap_first hx₁, assembledInverse, if_pos hn, collarBallInverse_map,
      D.first.left_inv hx₁]
  · have hne : D.second x ≠ 0 := fun h => hx ((D.second_eq_zero_iff hx₂).mp h)
    have hn := collarOuterMap_norm_gt hne
    rw [D.assembledMap_second hx₂, assembledInverse, if_neg (not_lt_of_ge hn.le),
      if_pos hn, collarOuterInverse_map, D.second.left_inv hx₂]
  · rw [D.assembledMap_central, assembledInverse, collarRadialMap_norm, collarRadius_zero,
      if_neg (lt_irrefl 2), if_neg (lt_irrefl 2), collarRadialInverse_map]

theorem assembledInverse_spec (q0 : UnitTwoSphere) (z : StandardCapSpace) :
    D.assembledInverse q0 z ∈ D.assembledSource ∧
      D.assembledMap (D.assembledInverse q0 z) = z := by
  rcases lt_trichotomy ‖z‖ 2 with hz | hz | hz
  · rw [assembledInverse, if_pos hz]
    have hx := D.first.map_target (D.mem_first_target (collarBallInverse z))
    refine ⟨D.first_mem_assembledSource hx, ?_⟩
    rw [D.assembledMap_first hx, D.first.right_inv (D.mem_first_target _)]
    exact collarBallMap_inverse (mem_ball_zero_iff.mpr hz)
  · have hn : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; norm_num)
    have hi : collarRadialInverse q0 z = (sphereNormalize q0 z, 0) := by
      simp only [collarRadialInverse, hz, collarHeight_two]
    rw [assembledInverse, hz, if_neg (lt_irrefl 2), if_neg (lt_irrefl 2), hi]
    refine ⟨D.neck_mem_assembledSource (D.central_mem_source _), ?_⟩
    rw [D.assembledMap_central, ← hi, collarRadialMap_inverse q0 hn]
  · rw [assembledInverse, if_neg (not_lt_of_ge hz.le), if_pos hz]
    have hx := D.second.map_target (D.mem_second_target (collarOuterInverse z))
    refine ⟨?_, ?_⟩
    · intro heq
      apply collarOuterInverse_ne_zero hz
      have h := D.second.right_inv (D.mem_second_target (collarOuterInverse z))
      rw [heq, D.second.right_inv (D.mem_second_target 0)] at h
      exact h.symm
    · rw [D.assembledMap_second hx, D.second.right_inv (D.mem_second_target _)]
      exact collarOuterMap_inverse hz

theorem assembledInverse_neck (q0 : UnitTwoSphere) {p : RoundCylinderSpace}
    (hp : p ∈ D.neck.source) :
    D.assembledInverse q0 (collarRadialMap p) = D.neck p := by
  rw [← D.assembledMap_neck hp]
  exact D.assembledInverse_map q0 (D.neck_mem_assembledSource hp)

theorem assembledInverse_eq_neck (q0 : UnitTwoSphere) {z : StandardCapSpace}
    (hz : z ≠ 0) (hp : collarRadialInverse q0 z ∈ D.neck.source) :
    D.assembledInverse q0 z = D.neck (collarRadialInverse q0 z) := by
  have h := D.assembledInverse_neck q0 hp
  rwa [collarRadialMap_inverse q0 hz] at h

theorem assembledInverse_zero (q0 : UnitTwoSphere) :
    D.assembledInverse q0 0 = D.first.symm 0 := by
  simp [assembledInverse]

theorem assembledMap_eq_zero_iff (q0 : UnitTwoSphere) {x : Y.carrier}
    (hx : x ∈ D.assembledSource) : D.assembledMap x = 0 ↔ x = D.first.symm 0 := by
  constructor
  · intro h
    have heq := D.assembledInverse_map q0 hx
    rw [h, D.assembledInverse_zero q0] at heq
    exact heq.symm
  · rintro rfl
    rw [D.assembledMap_first (D.first.map_target (D.mem_first_target 0)),
      D.first.right_inv (D.mem_first_target 0), collarBallMap_zero]

theorem assembledMap_swap (x : Y.carrier) :
    D.swap.assembledMap x = inversion 0 2 (D.assembledMap x) := by
  rcases D.cover_cases x with hx | hx | ⟨q, rfl⟩
  · rw [D.swap.assembledMap_second hx, D.assembledMap_first hx]
    rfl
  · rw [D.swap.assembledMap_first hx, D.assembledMap_second hx]
    exact (inversion_inversion 0 (by norm_num : (2 : ℝ) ≠ 0) (collarBallMap (D.second x))).symm
  · have hcenter : D.swap.neck (q, 0) = D.neck (q, 0) := by
      change D.neck (q, -0) = D.neck (q, 0)
      rw [neg_zero]
    calc
      D.swap.assembledMap (D.neck (q, 0)) = collarRadialMap (q, 0) := by
        rw [← hcenter, D.swap.assembledMap_central]
      _ = inversion 0 2 (D.assembledMap (D.neck (q, 0))) := by
        rw [D.assembledMap_central, collarRadialMap_reflect]
        simp only [collarReflect, neg_zero]

end PoincareConjecture.M74.CollarEndChartData
