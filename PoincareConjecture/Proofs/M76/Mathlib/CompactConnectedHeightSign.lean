import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X]




theorem IsCompact.exists_uniform_height_sign
    {S : Set X} (hS : IsCompact S) (hconn : IsConnected S)
    {f : X → ℝ} (hf : ContinuousOn f S) (hzero : ∀ x ∈ S, f x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      ((∀ x ∈ S, η ≤ f x) ∨ ∀ x ∈ S, f x ≤ -η) := by
  have horder := (hconn.isPreconnected.image f hf).ordConnected
  have hnot : (0 : ℝ) ∉ f '' S := by
    rintro ⟨x, hx, hxzero⟩
    exact hzero x hx hxzero
  obtain ⟨a, ha⟩ := hconn.nonempty
  obtain ⟨η, hη, hbound⟩ := hS.exists_forall_le' hf.abs
    (a := (0 : ℝ)) (fun x hx => abs_pos.mpr (hzero x hx))
  refine ⟨η, hη, ?_⟩
  rcases lt_or_gt_of_ne (hzero a ha) with hneg | hpos
  · right
    intro x hx
    have hxneg : f x < 0 := by
      by_contra h
      exact hnot (horder.out (mem_image_of_mem f ha) (mem_image_of_mem f hx)
        ⟨hneg.le, le_of_not_gt h⟩)
    have h := hbound x hx
    rw [abs_of_neg hxneg] at h
    linarith
  · left
    intro x hx
    have hxpos : 0 < f x := by
      by_contra h
      exact hnot (horder.out (mem_image_of_mem f hx) (mem_image_of_mem f ha)
        ⟨le_of_not_gt h, hpos.le⟩)
    simpa only [abs_of_pos hxpos] using hbound x hx

end Set
