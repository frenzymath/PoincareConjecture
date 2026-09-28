import PoincareConjecture.Proofs.M38.RetainedComponentLabels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier]

namespace EventCapCoordinates

variable {i : Fin (F.event T hT).cap_count} (P : EventCapCoordinates F T hT i)

theorem retained_ball_inverse_negative (x : eventCapComplementOpen F T hT)
    (hx : x.val ∈ P.ball.map '' Metric.ball (0 : StandardCapSpace) 2) :
    (F.event T hT).retention.inverse x.val ∈
      P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) := by
  obtain ⟨z, hz, hzx⟩ := hx
  have houter : 1 < ‖z‖ := (P.ball_mem_cap_complement_iff hz).mp (hzx.symm ▸ x.property)
  have hinner : ‖z‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hs : 1 - ‖z‖ ∈ Set.Ioo (-1 : ℝ) 0 := by
    constructor <;> linarith
  have heq := P.negative_gluing (capUnitDirection z) (1 - ‖z‖) hs
  rw [show 1 - (1 - ‖z‖) = ‖z‖ by ring, capUnitDirection_radial, hzx] at heq
  exact ⟨(capUnitDirection z, 1 - ‖z‖), ⟨Set.mem_univ _, hs⟩, heq⟩

end EventCapCoordinates

variable (F T hT) (P : ∀ i, EventCapCoordinates F T hT i)

theorem retained_ball_patches_disjoint (i j : Fin (F.event T hT).cap_count) (hij : i ≠ j) :
    Disjoint ((P i).ball.map '' Metric.ball (0 : StandardCapSpace) 2)
      ((P j).ball.map '' Metric.ball (0 : StandardCapSpace) 2) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hx : x ∈ eventCapComplementOpen F T hT := retained_ball_overlap F T hT P i j hij x hxi hxj
  have hni := (P i).retained_ball_inverse_negative ⟨x, hx⟩ hxi
  have hnj := (P j).retained_ball_inverse_negative ⟨x, hx⟩ hxj
  have hsub : (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (-1 : ℝ) 0 ⊆
      Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans zero_lt_one⟩
  exact Set.disjoint_left.mp ((P i).collars_disjoint (P j) hij)
    (Set.image_mono hsub hni) (Set.image_mono hsub hnj)

end PoincareConjecture.M38
