import PoincareConjecture.Proofs.M14.Sec6_2_IntervalLift
import PoincareConjecture.Definitions.M14GeneralizedLGeometry











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M14

variable {K : SpacetimeInterval} (J : SmoothSpacetimeInterval K)



noncomputable def ordinaryCaptureClock (t₀ : J.Point) (T s : ℝ) : J.Point :=
  by
    classical
    exact if h : T - s ∈ K.domain then ⟨T - s, h⟩ else t₀



theorem ordinaryCaptureClock_val (t₀ : J.Point) (T : ℝ) {s : ℝ}
    (hs : T - s ∈ K.domain) : (ordinaryCaptureClock J t₀ T s).val = T - s := by
  simp only [ordinaryCaptureClock, dif_pos hs]



theorem ordinaryCaptureClock_zero (t₀ : J.Point) :
    ordinaryCaptureClock J t₀ t₀.val 0 = t₀ := by
  apply Subtype.ext
  simpa only [sub_zero] using ordinaryCaptureClock_val J t₀ t₀.val
    (show t₀.val - 0 ∈ K.domain by simpa only [sub_zero] using t₀.property)



theorem ordinaryCaptureClock_contMDiffOn (t₀ : J.Point) (T : ℝ) {S : Set ℝ}
    (hS : ∀ s ∈ S, T - s ∈ K.domain) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ (ordinaryCaptureClock J t₀ T) S := by
  apply intervalLift_contMDiffOn
  exact (contMDiff_const.sub contMDiff_id).contMDiffOn.congr
    (fun s hs => ordinaryCaptureClock_val J t₀ T (hS s hs))

end PoincareConjecture.M14
