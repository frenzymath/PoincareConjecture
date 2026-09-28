import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30.PartialPointedMetricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
  (G : PartialPointedMetricConvergence g p A)





theorem tendstoUniformlyOn_static_stage_metric_jets (j N : ℕ) :
    let Y : TopologicalSpace.Opens G.limitCarrier.carrier :=
      ⟨G.exhaustion j, G.exhaustion_open j⟩
    ∀ h : ℕ → RiemannianMetric n Y,
      (∀ (k : ℕ) (x : Y) (v w : TangentSpace (𝓡 n) x),
        (h k).inner x v w = (g (G.subsequence (k + N))).inner
          (G.embedding (k + N) x.val)
          (mfderiv (𝓡 n) (𝓡 n) (fun y : Y => G.embedding (k + N) y.val) x v)
          (mfderiv (𝓡 n) (𝓡 n) (fun y : Y => G.embedding (k + N) y.val) x w)) →
      ∀ (q : G.limitCarrier.carrier) (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V → V ⊆ (extChartAt (𝓡 n) q).target →
        ∀ ψ : EuclideanSpace ℝ (Fin n) → Y,
          ContMDiffOn (𝓡 n) (𝓡 n) ∞ ψ V →
          (∀ z ∈ V, (ψ z).val = (extChartAt (𝓡 n) q).symm z) →
          ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m ((h k).pullbackCoefficients ψ))
            (iteratedFDeriv ℝ m (G.limitMetric.pullbackCoefficients
              (extChartAt (𝓡 n) q).symm)) atTop K := by
  intro Y h hmetric q V hV hVc ψ hψ hψval m K hK hKV
  let c := extChartAt (𝓡 n) q
  have hcoeff : ∀ᶠ k in atTop, EqOn ((h k).pullbackCoefficients ψ)
      ((g (G.subsequence (k + N))).pullbackCoefficients
        (G.embedding (k + N) ∘ c.symm)) V := by
    filter_upwards [eventually_ge_atTop j] with k hk
    let f : Y → M (G.subsequence (k + N)) := fun x => G.embedding (k + N) x.val
    have hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f := by
      intro x
      exact ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) Y x).comp (𝓡 n)
        (M (G.subsequence (k + N)))
        (G.embedding_smooth (k + N)
          ⟨x.val, G.exhaustion_monotone (by omega) x.property⟩)).contMDiffAt
    intro z hz
    have hψz := (hψ z hz).contMDiffAt (hV.mem_nhds hz)
    have heq : f ∘ ψ =ᶠ[𝓝 z] G.embedding (k + N) ∘ c.symm := by
      filter_upwards [hV.mem_nhds hz] with y hy
      exact congrArg (G.embedding (k + N)) (hψval y hy)
    have hd := (mfderiv_comp z ((hf (ψ z)).mdifferentiableAt (by simp))
      (hψz.mdifferentiableAt (by simp))).symm.trans heq.mfderiv_eq
    ext v w
    change (h k).inner (ψ z) (mfderiv (𝓡 n) (𝓡 n) ψ z v)
      (mfderiv (𝓡 n) (𝓡 n) ψ z w) = _
    rw [hmetric]
    change (g (G.subsequence (k + N))).inner (f (ψ z))
        (mfderiv (𝓡 n) (𝓡 n) f (ψ z) (mfderiv (𝓡 n) (𝓡 n) ψ z v))
        (mfderiv (𝓡 n) (𝓡 n) f (ψ z) (mfderiv (𝓡 n) (𝓡 n) ψ z w)) = _
    have hp : f (ψ z) = G.embedding (k + N) (c.symm z) := heq.self_of_nhds
    erw [congrArg (fun L => L v) hd, congrArg (fun L => L w) hd, hp]
    rfl
  have hconv := G.metric_jets q m K hK (hKV.trans hVc)
  have hshift : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g (G.subsequence (k + N))).pullbackCoefficients
        (G.embedding (k + N) ∘ c.symm)))
      (iteratedFDeriv ℝ m (G.limitMetric.pullbackCoefficients c.symm)) atTop K :=
    fun E hE => (tendsto_add_atTop_nat N).eventually (hconv E hE)
  apply hshift.congr
  filter_upwards [hcoeff] with k hk z hz
  have heq : (h k).pullbackCoefficients ψ =ᶠ[𝓝 z]
      (g (G.subsequence (k + N))).pullbackCoefficients
        (G.embedding (k + N) ∘ c.symm) := by
    filter_upwards [hV.mem_nhds (hKV hz)] with y hy
    exact hk hy
  exact ((heq.iteratedFDeriv ℝ m).self_of_nhds).symm

end PoincareConjecture.M30.PartialPointedMetricConvergence
