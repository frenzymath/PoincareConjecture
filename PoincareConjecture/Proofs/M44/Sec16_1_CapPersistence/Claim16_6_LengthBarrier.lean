import PoincareConjecture.Proofs.M44.Mathlib.FirstExit
import PoincareConjecture.Proofs.M36.MetricComparison










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.RiemannianMetric

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]




theorem ball_subset_of_inverse_length_barrier
    (g : RiemannianMetric 3 X) (k : RiemannianMetric 3 Y)
    (f : X → Y) {U : Set X} (hU : IsOpen U) {p : X} (hp : p ∈ U)
    (hf : ∀ x ∈ closure U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ closure U, ∀ v : TangentSpace (𝓡 3) x,
      k.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ g.inner x v v)
    {r : ℝ} (hboundary : ∀ x ∈ frontier U,
      ENNReal.ofReal r ≤ k.edist (f p) (f x)) :
    g.ball p r ⊆ U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro q hq
  by_contra hnot
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hq
  obtain ⟨c, hc, hfront, _, hmaps⟩ :=
    hγ.continuousOn.exists_first_frontier_time zero_le_one hU
      (hγ0 ▸ hp) (hγ1 ▸ hnot)
  have hbound := M36.edist_comp_le_pathELength_of_pullback_bound g k hf hmetric
    hc.1.le (hγ.mono (Icc_subset_Icc le_rfl hc.2)) hmaps.image_subset
  rw [hγ0] at hbound
  have hsegment := M36.metric_pathELength_mono g γ (a := 0) (b := 1) le_rfl hc.2
  exact (not_lt_of_ge ((hboundary _ hfront).trans (hbound.trans hsegment))) hlength




theorem isCompact_closure_ball_of_inverse_length_barrier [T2Space X]
    (g : RiemannianMetric 3 X) (k : RiemannianMetric 3 Y)
    (f : X → Y) {U : Set X} (hU : IsOpen U)
    (hcompact : IsCompact (closure U)) {p : X} (hp : p ∈ U)
    (hf : ∀ x ∈ closure U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ closure U, ∀ v : TangentSpace (𝓡 3) x,
      k.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ g.inner x v v)
    {r : ℝ} (hboundary : ∀ x ∈ frontier U,
      ENNReal.ofReal r ≤ k.edist (f p) (f x)) :
    IsCompact (closure (g.ball p r)) :=
  hcompact.of_isClosed_subset isClosed_closure
    (closure_mono (g.ball_subset_of_inverse_length_barrier k f hU hp hf hmetric hboundary))

end PoincareConjecture.RiemannianMetric
