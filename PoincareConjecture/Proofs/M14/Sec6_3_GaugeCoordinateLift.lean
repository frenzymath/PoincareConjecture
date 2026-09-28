import PoincareConjecture.Proofs.M14.Sec6_2_IntervalLift
import PoincareConjecture.Definitions.M14GeneralizedLGeometry










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




theorem exists_smooth_gaugeLift_of_coordinates (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) (T : ℝ) {C : Set ℝ}
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} (hq : ContDiffOn ℝ ∞ q C)
    (hmap : MapsTo q C (extChartAt (𝓡 n) x₀).target) :
    ∃ β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b,
      ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β C ∧
      (∀ s ∈ C, (β s).1.val = T - s ^ 2) ∧ ∀ s ∈ C, (β s).2.val = q s := by
  classical
  let t : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point := fun s =>
    if hs : T - s ^ 2 ∈ (G.gaugeCover.interval b).domain then ⟨T - s ^ 2, hs⟩ else t₀
  have hclock (s : ℝ) (hs : s ∈ C) : (t s).val = T - s ^ 2 := by
    simp only [t, dif_pos (htime s hs)]
  have ht : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ t C := by
    apply intervalLift_contMDiffOn (𝓘(ℝ, ℝ))
      (G.timeIntervals.interval (G.gaugeCover.interval b))
    exact ((contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn).congr hclock
  let z := fun s => (extChartAt (𝓡 n) x₀).symm (q s)
  have hz : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ z C :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x₀).comp hq.contMDiffOn hmap
  refine ⟨fun s => (t s, z s), ht.prodMk hz, hclock, ?_⟩
  intro s hs
  have hval : extChartAt (𝓡 n) x₀ (z s) = (z s).val := by rw [extChartAt_coe]; rfl
  rw [← hval]
  exact (extChartAt (𝓡 n) x₀).right_inv (hmap hs)

end PoincareConjecture.M14
