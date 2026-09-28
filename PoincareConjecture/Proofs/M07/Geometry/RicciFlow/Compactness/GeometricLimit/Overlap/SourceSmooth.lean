import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceTransition
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem contMDiffOn_invFun_of_localDiffeomorph
    {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 n) ∞ Y] [Nonempty X]
    {f : X → Y} (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hinj : Function.Injective f) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Function.invFun f) (range f) := by
  rintro _ ⟨x, rfl⟩
  apply ContMDiffAt.contMDiffWithinAt
  exact Poincare.contMDiffAt_of_local_left_inverse (hf.contMDiff x)
    (hf.mfderivToContinuousLinearEquiv (by simp) x).bijective
    (Eventually.of_forall (Function.leftInverse_invFun hinj))

variable {ι : Type*} {n : ℕ} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, LocallyCompactSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold (𝓡 n) ∞ (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, X i × X j → ℝ}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn hsmooth in
theorem exists_eventually_smooth_source_transition {i j : ι} {x : X i}
    (hx : x ∈ overlap D i j) :
    ∃ U : Set (X i), IsOpen U ∧ x ∈ U ∧ U ⊆ overlap D i j ∧
      ∀ᶠ k in atTop, ContMDiffOn (𝓡 n) (𝓡 n) ∞
        (fun y => Function.invFun (e k j) (e k i y)) U := by
  obtain ⟨U, hU, hxU, K, _, hrep⟩ :=
    exists_source_transition_neighborhood hD L he c hc hlower hopen hconn hx
  refine ⟨U ∩ overlap D i j,
    hU.inter (isOpen_overlap hD L he c hc hlower hopen hconn i j),
    ⟨hxU, hx⟩, inter_subset_right, ?_⟩
  filter_upwards [hrep] with k hk
  exact (contMDiffOn_invFun_of_localDiffeomorph (hsmooth k j) (hopen k j).injective).comp
    (hsmooth k i).contMDiff.contMDiffOn
    (fun y hy => image_subset_range _ _ (hk y hy.1).1)

end PoincareConjecture.ChartDistance
