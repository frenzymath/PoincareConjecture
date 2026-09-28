import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.SpatialBounds
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinFlowJetBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M28

set_option synthInstance.maxHeartbeats 100000 in

theorem eventually_within_bounds_closed_backward_of_curvature
    {n : ℕ} {α : Type*} {M : α → Type*}
    [∀ w, TopologicalSpace (M w)]
    [∀ w, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M w)]
    [∀ w, IsManifold (𝓡 n) ∞ (M w)]
    (l : Filter α) {tau : ℝ} (htau : 0 < tau)
    (F : ∀ w, RicciFlow n (M w) (Icc (-tau) 0))
    (U V : α → Set (EuclideanSpace ℝ (Fin n)))
    (e : ∀ w, EuclideanSpace ℝ (Fin n) → M w)
    (hU : ∀ w, IsOpen (U w)) (hVU : ∀ w, V w ⊆ U w)
    (he : ∀ w, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e w) (U w))
    (hi : ∀ w y, y ∈ U w → (mfderiv (𝓡 n) (𝓡 n) (e w) y).IsInvertible)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hell : ∀ᶠ w in l, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ V w, ∀ v,
      a * ‖v‖ ^ 2 ≤ ((F w).metric t).pullbackCoefficients (e w) x v v ∧
        ((F w).metric t).pullbackCoefficients (e w) x v v ≤ b * ‖v‖ ^ 2)
    (hcurv : ∀ s, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ w in l,
      ∀ t ∈ Ioo (-tau) 0, ∀ x ∈ V w,
        ((F w).connection t).curvatureDerivativeNorm s (e w x) ≤ K)
    (hinit : ∀ m, ∃ Z : ℝ, 0 ≤ Z ∧ ∀ᶠ w in l, ∀ x ∈ V w,
      ‖iteratedFDeriv ℝ m (((F w).metric 0).pullbackCoefficients (e w)) x‖ ≤ Z) :
    ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l,
      ∀ z ∈ Icc (-tau) 0 ×ˢ V w,
        ‖iteratedFDerivWithin ℝ m
          (fun z => ((F w).metric z.1).pullbackCoefficients (e w) z.2)
          (Icc (-tau) 0 ×ˢ U w) z‖ ≤ B := by
  have hspatial := eventually_spatial_bounds_closed_backward l htau F U V e
    hU hVU he hi ha hb hell hcurv hinit
  apply RicciFlow.eventuallyBounded_within_pullbackCoefficients_of_spatial_bounds
    l (fun _ => Icc (-tau) 0) F U e
    (fun w => Ioo (-tau) 0 ×ˢ V w) (fun w => Icc (-tau) 0 ×ˢ V w)
    (fun _ => uniqueDiffOn_Icc (by linarith : -tau < 0)) hU he hi
  · intro w z hz
    exact ⟨by simpa only [interior_Icc] using hz.1, hVU w hz.2⟩
  · intro w z hz
    refine ⟨⟨hz.1, hVU w hz.2⟩, ?_⟩
    rw [closure_prod_eq, closure_Ioo (by linarith : (-tau : ℝ) ≠ 0)]
    exact ⟨hz.1, subset_closure hz.2⟩
  · intro q
    obtain ⟨B, hB, hbound⟩ := hspatial q
    exact ⟨B, hB, hbound.mono (fun w hw z hz j hj =>
      hw z.1 (Ioo_subset_Icc_self hz.1) z.2 hz.2 j hj)⟩
  · exact ha
  · exact hell.mono (fun w hw z hz v =>
      (hw z.1 (Ioo_subset_Icc_self hz.1) z.2 hz.2 v).1)

end PoincareConjecture.M28
