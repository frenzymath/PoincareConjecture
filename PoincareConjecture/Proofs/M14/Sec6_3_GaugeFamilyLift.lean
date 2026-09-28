import PoincareConjecture.Proofs.M14.Sec6_2_IntervalLift
import PoincareConjecture.Definitions.M14GeneralizedLGeometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (IM : ModelWithCorners ℝ E H) {N : Type v} [TopologicalSpace N] [ChartedSpace H N]

theorem exists_smooth_gaugeLift_of_maps (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) {S : Set N} {c : N → ℝ}
    (hc : ContMDiffOn IM (𝓘(ℝ, ℝ)) ∞ c S)
    (htime : MapsTo c S (G.gaugeCover.interval b).domain)
    {q : N → EuclideanSpace ℝ (Fin n)} (hq : ContMDiffOn IM (𝓡 n) ∞ q S)
    (hmap : MapsTo q S (extChartAt (𝓡 n) x₀).target) :
    ∃ β : N → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b,
      ContMDiffOn IM (spacetimeModel n) ∞ β S ∧
      (∀ z ∈ S, (β z).1.val = c z) ∧ ∀ z ∈ S, (β z).2.val = q z := by
  classical
  let t : N → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point := fun z =>
    if hz : c z ∈ (G.gaugeCover.interval b).domain then ⟨c z, hz⟩ else t₀
  have hclock (z : N) (hz : z ∈ S) : (t z).val = c z := by
    simp only [t, dif_pos (htime hz)]
  have ht : ContMDiffOn IM (𝓡∂ 1) ∞ t S :=
    intervalLift_contMDiffOn IM (G.timeIntervals.interval (G.gaugeCover.interval b))
      (hc.congr hclock)
  let p := fun z => (extChartAt (𝓡 n) x₀).symm (q z)
  have hp : ContMDiffOn IM (𝓡 n) ∞ p S :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x₀).comp hq hmap
  refine ⟨fun z => (t z, p z), ht.prodMk hp, hclock, ?_⟩
  intro z hz
  have hval : extChartAt (𝓡 n) x₀ (p z) = (p z).val := by rw [extChartAt_coe]; rfl
  rw [← hval]
  exact (extChartAt (𝓡 n) x₀).right_inv (hmap hz)

end PoincareConjecture.M14
