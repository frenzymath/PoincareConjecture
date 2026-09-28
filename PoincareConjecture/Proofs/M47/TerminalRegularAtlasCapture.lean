import PoincareConjecture.Proofs.M47.TerminalCurvatureCompactBuffers
import Mathlib.Topology.UniformSpace.UniformConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalSource_compact_atlas_image_radius
    {ι : Type u} {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T3Space X]
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcover : ∀ x : X, ∃ i, x ∈ (c i).source)
    (M : ℕ → Type w) [∀ k, MetricSpace (M k)]
    (point : ∀ k, M k) (f : ∀ k, X → M k) (e : ∀ k, ι → E → M k)
    (b : ι → ℝ)
    (hbase : ∀ k i z, z ∈ (c i).target → dist (point k) (e k i z) ≤ b i)
    (happrox : ∀ i K, IsCompact K → K ⊆ (c i).target →
      TendstoUniformlyOn (fun k z => dist (f k ((c i).symm z)) (e k i z))
        (fun _ => 0) atTop K)
    {C : Set X} (hC : IsCompact C) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ k in atTop, MapsTo (f k) C (Metric.ball (point k) R) := by
  classical
  rcases C.eq_empty_or_nonempty with hCempty | hCne
  · refine ⟨1, zero_lt_one, Filter.Eventually.of_forall ?_⟩
    intro k
    simp only [hCempty, mapsTo_empty]
  obtain ⟨s, _hs, index, K, hK, htarget, hfinite⟩ :=
    terminalCurvature_exists_finite_original_chart_buffers c hC hCne
      (fun x _ => hcover x)
  let R : ℝ := 2 + ∑ j : s, max (b (index j)) 0
  have hsum : 0 ≤ ∑ j : s, max (b (index j)) 0 :=
    Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have htail : ∀ᶠ k in atTop, ∀ j : s, ∀ z ∈ K j,
      dist (f k ((c (index j)).symm z)) (e k (index j) z) < 1 := by
    apply Filter.eventually_all.mpr
    intro j
    have ht := (Metric.tendstoUniformlyOn_iff.mp
      (happrox (index j) (K j) (hK j) (htarget j))) 1 zero_lt_one
    filter_upwards [ht] with k hk
    intro z hz
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] using hk z hz
  refine ⟨R, by dsimp only [R]; linarith, ?_⟩
  filter_upwards [htail] with k hk
  intro x hx
  obtain ⟨j, hsource, hcoord⟩ := hfinite x hx
  have herror := hk j (c (index j) x) hcoord
  have hinverse : (c (index j)).symm (c (index j) x) = x :=
    (c (index j)).left_inv hsource
  change dist (f k ((c (index j)).symm (c (index j) x)))
    (e k (index j) (c (index j) x)) < 1 at herror
  rw [hinverse] at herror
  have hb := hbase k (index j) (c (index j) x) (htarget j hcoord)
  have hentry : b (index j) ≤ ∑ i : s, max (b (index i)) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum
      (fun i _ => le_max_right (b (index i)) 0) (Finset.mem_univ j))
  have htriangle := dist_triangle (point k) (e k (index j) (c (index j) x)) (f k x)
  rw [dist_comm (e k (index j) (c (index j) x)) (f k x)] at htriangle
  rw [Metric.mem_ball, dist_comm]
  dsimp only [R]
  linarith

end PoincareConjecture.M47
