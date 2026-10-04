import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.IntervalLift
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic

/-!
# The actual backward clock in a captured interval

Morgan-Tian Definition 3.38, p. 61, and Definitions 6.1 and 6.7,
pp. 105, 108. The total clock uses an arbitrary fixed interval point
outside its valid range. On every stated valid set its actual value is
T-s, and M13's interval charts give within smoothness, including the
closed square-time endpoints used to identify normalized initial data.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M14

variable {K : SpacetimeInterval} (J : SmoothSpacetimeInterval K)

/-- A total lift of the actual backward clock with a fixed value only
outside the valid interval, Definition 6.1, p. 105. -/
noncomputable def ordinaryCaptureClock (t₀ : J.Point) (T s : ℝ) : J.Point :=
  by
    classical
    exact if h : T - s ∈ K.domain then ⟨T - s, h⟩ else t₀

/-- The clock equals its prescribed real value on its valid domain,
Definition 6.1, p. 105. -/
theorem ordinaryCaptureClock_val (t₀ : J.Point) (T : ℝ) {s : ℝ}
    (hs : T - s ∈ K.domain) : (ordinaryCaptureClock J t₀ T s).val = T - s := by
  simp only [ordinaryCaptureClock, dif_pos hs]

/-- At elapsed time zero the lifted clock recovers its actual base
interval point, Definition 6.1, p. 105. -/
theorem ordinaryCaptureClock_zero (t₀ : J.Point) :
    ordinaryCaptureClock J t₀ t₀.val 0 = t₀ := by
  apply Subtype.ext
  simpa only [sub_zero] using ordinaryCaptureClock_val J t₀ t₀.val
    (show t₀.val - 0 ∈ K.domain by simpa only [sub_zero] using t₀.property)

/-- Smoothness holds within every actual valid backward-time set,
including interval endpoints, Definition 3.38, p. 61. -/
theorem ordinaryCaptureClock_contMDiffOn (t₀ : J.Point) (T : ℝ) {S : Set ℝ}
    (hS : ∀ s ∈ S, T - s ∈ K.domain) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ (ordinaryCaptureClock J t₀ T) S := by
  apply intervalLift_contMDiffOn
  exact (contMDiff_const.sub contMDiff_id).contMDiffOn.congr
    (fun s hs => ordinaryCaptureClock_val J t₀ T (hS s hs))

end PoincareMT.M14
