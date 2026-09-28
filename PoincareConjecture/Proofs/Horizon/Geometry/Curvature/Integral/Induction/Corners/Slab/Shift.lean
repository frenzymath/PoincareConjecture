import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

open Set
theorem IsProperMap.restrictPreimage_shifted_interval
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} {b s : ℝ}
    (h : IsProperMap ((Ioo (b - s / 16) (b + s / 16)).restrictPreimage f)) :
    IsProperMap ((Ioo (0 : ℝ) (s / 8)).restrictPreimage
      (fun x => f x - b + s / 16)) := by
  have hinterval (x : ℝ) :
      x ∈ Ioo (b - s / 16) (b + s / 16) ↔
        x - b + s / 16 ∈ Ioo (0 : ℝ) (s / 8) := by
    simp only [mem_Ioo]
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
  let target : Ioo (b - s / 16) (b + s / 16) ≃ₜ Ioo (0 : ℝ) (s / 8) :=
    ((Homeomorph.subRight b).trans (Homeomorph.addRight (s / 16))).subtype hinterval
  let source :
      ((fun x => f x - b + s / 16) ⁻¹' Ioo (0 : ℝ) (s / 8)) ≃ₜ
        (f ⁻¹' Ioo (b - s / 16) (b + s / 16)) :=
    (Homeomorph.refl X).subtype (fun x => (hinterval (f x)).symm)
  exact (target.isProperMap.comp h).comp source.isProperMap
