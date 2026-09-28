import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

set_option autoImplicit false

open Set

namespace Poincare.CurvatureIntegral

theorem exists_finite_punctured_ball_cover
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) :
    ∃ F S : Finset X,
      (S : Set X) = {x | x ∈ K ∧ ∀ y, y ≠ x → b y ≤ dist y x} ∧
      K \ (S : Set X) ⊆ ⋃ y ∈ F, Metric.ball y (b y) \ {y} := by
  classical
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun x => Metric.ball x (b x))
    (fun _ => Metric.isOpen_ball) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hb x)⟩)
  let S : Set X := {x | x ∈ K ∧ ∀ y, y ≠ x → b y ≤ dist y x}
  have hSF : S ⊆ (F : Set X) := by
    intro x hx
    obtain ⟨y, hyF, hxy⟩ := mem_iUnion₂.mp (hF hx.1)
    by_contra hxF
    have hyx : y ≠ x := by
      intro hyx
      exact hxF (hyx ▸ hyF)
    have hle := hx.2 y hyx
    exact (not_lt_of_ge hle) (by simpa only [Metric.mem_ball, dist_comm] using hxy)
  have hS : S.Finite := F.finite_toSet.subset hSF
  have hw : ∀ x : X, ∃ y : X,
      ¬ (∀ z, z ≠ x → b z ≤ dist z x) → x ∈ Metric.ball y (b y) \ {y} := by
    intro x
    by_cases hx : ∀ z, z ≠ x → b z ≤ dist z x
    · exact ⟨x, fun h => False.elim (h hx)⟩
    · push Not at hx
      obtain ⟨y, hyx, hxy⟩ := hx
      refine ⟨y, fun _ => ⟨?_, ?_⟩⟩
      · simpa only [Metric.mem_ball, dist_comm] using hxy
      · exact fun h => hyx (mem_singleton_iff.mp h).symm
  choose c hc using hw
  refine ⟨F ∪ F.image c, hS.toFinset, hS.coe_toFinset, ?_⟩
  intro x hx
  have hxS : x ∉ S := by simpa only [hS.coe_toFinset] using hx.2
  have hxreg : ¬ (∀ z, z ≠ x → b z ≤ dist z x) := by
    exact fun h => hxS ⟨hx.1, h⟩
  obtain ⟨y, hyF, hxy⟩ := mem_iUnion₂.mp (hF hx.1)
  by_cases hxy' : x = y
  · subst y
    refine mem_iUnion₂.mpr ⟨c x, Finset.mem_union_right _ ?_, hc x hxreg⟩
    exact Finset.mem_image.mpr ⟨x, hyF, rfl⟩
  · exact mem_iUnion₂.mpr
      ⟨y, Finset.mem_union_left _ hyF, hxy, fun h => hxy' (mem_singleton_iff.mp h)⟩

theorem finite_spires_of_isCompact
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) :
    {x | x ∈ K ∧ ∀ y, y ≠ x → b y ≤ dist y x}.Finite := by
  obtain ⟨_, S, hS, _⟩ := exists_finite_punctured_ball_cover hK b hb
  rw [← hS]
  exact S.finite_toSet

end Poincare.CurvatureIntegral
