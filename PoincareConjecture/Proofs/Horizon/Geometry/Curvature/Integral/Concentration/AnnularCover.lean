import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open Set

namespace Poincare.CurvatureIntegral

theorem exists_finite_radial_annulus_cover
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K) (p : X)
    {A B r0 : ℝ} (hA : 0 < A) (hAB : A < B) (hr0 : 0 < r0)
    (hsub : K ⊆ {x | 0 < dist p x ∧ dist p x < B * r0}) :
    ∃ F : Finset ℝ, (∀ r ∈ F, 0 < r ∧ r ≤ r0) ∧
      K ⊆ ⋃ r ∈ F, {x | A * r < dist p x ∧ dist p x < B * r} := by
  classical
  have hB : 0 < B := hA.trans hAB
  have hcover : K ⊆ ⋃ r ∈ Ioc (0 : ℝ) r0,
      {x | A * r < dist p x ∧ dist p x < B * r} := by
    intro x hx
    obtain ⟨hd, hdr0⟩ := hsub hx
    have hlow : dist p x / B < min r0 (dist p x / A) := by
      apply lt_min
      · exact (div_lt_iff₀ hB).mpr (by simpa only [mul_comm] using hdr0)
      · exact div_lt_div_of_pos_left hd hA hAB
    obtain ⟨r, hr, hr'⟩ := exists_between
      (max_lt (lt_min hr0 (div_pos hd hA)) hlow)
    have hpos : 0 < r := (le_max_left _ _).trans_lt hr
    have hBr : dist p x / B < r := (le_max_right _ _).trans_lt hr
    have hrA : r < dist p x / A := hr'.trans_le (min_le_right _ _)
    refine mem_iUnion₂.mpr ⟨r, ⟨hpos, hr'.le.trans (min_le_left _ _)⟩, ?_, ?_⟩
    · simpa only [mul_comm] using (lt_div_iff₀ hA).mp hrA
    · simpa only [mul_comm] using (div_lt_iff₀ hB).mp hBr
  obtain ⟨S, hS, hfinite, hcover⟩ := hK.elim_finite_subcover_image
    (b := Ioc (0 : ℝ) r0)
    (c := fun r => {x | A * r < dist p x ∧ dist p x < B * r})
    (fun _ _ => (isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
      (isOpen_lt (continuous_const.dist continuous_id) continuous_const)) hcover
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro r hr
    exact hS (hfinite.mem_toFinset.mp hr)
  · simpa only [hfinite.mem_toFinset] using hcover

end Poincare.CurvatureIntegral
