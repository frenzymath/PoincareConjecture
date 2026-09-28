import PoincareConjecture.Proofs.M76.Mathlib.RelativeFinitePLApproximation

set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

theorem exists_relative_finitePL_approximation_with_compact_control
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → F} (hf : ContinuousOn f K.space) {S : Set E}
    (hSK : S ⊆ K.space) (hfS : FinitePiecewiseAffineOn f S)
    {W V : Set F} (hW : IsOpen W) (hfW : MapsTo f K.space W)
    {B : Set E} (hB : IsCompact B) (hBK : B ⊆ K.space)
    (hV : IsOpen V) (hfV : MapsTo f B V) :
    ∃ g : E → F, FinitePiecewiseAffineOn g K.space ∧ EqOn g f S ∧
      (∀ x ∈ K.space, segment ℝ (f x) (g x) ⊆ W) ∧
      ∀ x ∈ B, segment ℝ (f x) (g x) ⊆ V := by
  have hfull : IsCompact (f '' K.space) :=
    (K.isCompact_space_of_finite hK).image_of_continuousOn hf
  have hpart : IsCompact (f '' B) := hB.image_of_continuousOn (hf.mono hBK)
  obtain ⟨r, hr, hrW⟩ := hfull.exists_thickening_subset_open hW hfW.image_subset
  obtain ⟨s, hs, hsV⟩ := hpart.exists_thickening_subset_open hV hfV.image_subset
  obtain ⟨g, L, hL, hLK, hg, _, hfix, herror⟩ :=
    K.exists_relative_finitePL_approximation hK hf hSK hfS (lt_min hr hs)
  have hball (x : E) (hx : x ∈ K.space) :
      segment ℝ (f x) (g x) ⊆ ball (f x) (min r s) :=
    (convex_ball (f x) (min r s)).segment_subset (mem_ball_self (lt_min hr hs))
      (by simpa only [mem_ball, dist_eq_norm] using herror x hx)
  refine ⟨g, ⟨L, hL, hLK.space_eq, hg⟩, hfix, ?_, ?_⟩
  · intro x hx y hy
    apply hrW
    exact mem_thickening_iff.mpr ⟨f x, mem_image_of_mem f hx,
      lt_of_lt_of_le (hball x hx hy) (min_le_left r s)⟩
  · intro x hx y hy
    apply hsV
    exact mem_thickening_iff.mpr ⟨f x, mem_image_of_mem f hx,
      lt_of_lt_of_le (hball x (hBK hx) hy) (min_le_right r s)⟩

end Geometry.SimplicialComplex
