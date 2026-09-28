import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.SquareModulus
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Metrizable.Uniformity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal BoundedContinuousFunction

universe u

namespace PoincareConjecture.Proofs.M46

private theorem uniform_subsequence_of_compact_range {A Z : Type*}
    [TopologicalSpace A] [CompactSpace A] [EMetricSpace Z]
    (f : ℕ → A → Z) (hf : Equicontinuous f) {K : Set Z} (hK : IsCompact K)
    (hfK : ∀ k s, f k s ∈ K) :
    ∃ g : C(A, Z), ∃ phi : ℕ → ℕ, StrictMono phi ∧
      TendstoUniformly (fun k => f (phi k)) g atTop := by
  classical
  let : MetricSpace Z := UniformSpace.metricSpace Z
  have hf' : Equicontinuous f := by
    with_reducible_and_instances exact hf
  let F : ℕ → A →ᵇ Z := fun k =>
    BoundedContinuousFunction.mkOfCompact ⟨f k, hf.continuous k⟩
  have hF : Equicontinuous (fun g : range F => (g.val : A → Z)) := by
    have h := hf'.comp (fun g : range F => Classical.choose g.property)
    convert h using 1
    funext g s
    have hg := congrArg (fun q : A →ᵇ Z => q s) (Classical.choose_spec g.property)
    exact hg.symm
  have hcompact := BoundedContinuousFunction.arzela_ascoli K hK (range F)
    (by rintro _ s ⟨k, rfl⟩; exact hfK k s) hF
  obtain ⟨g, _, phi, hphi, hlim⟩ := hcompact.tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  exact ⟨g.toContinuousMap, phi, hphi,
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim⟩

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T tau : ℝ} {x y : G.Point}




theorem backward_squarePaths_uniform_subsequence
    (p : ℕ → M14BackwardPath G T 0 tau x y) {D : ℝ} (hD : 0 ≤ D)
    (henergy : ∀ k, IntervalIntegrable (M14.pathSquareKinetic (p k)) volume 0 (Real.sqrt tau) ∧
      (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic (p k) s) ≤ D)
    {K : Set G.Point} (hK : IsCompact K)
    (hpaths : ∀ k, MapsTo (p k).curve (Icc 0 tau) K) :
    let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
      ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
    let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
    ∃ (alpha : C(Icc 0 (Real.sqrt tau), G.Point)) (phi : ℕ → ℕ), StrictMono phi ∧
      TendstoUniformly (fun k (s : Icc 0 (Real.sqrt tau)) =>
        (p (phi k)).curve (s.val ^ 2)) alpha atTop ∧
      (∀ s, alpha s ∈ K) ∧
      (∀ s, G.spacetime.timeFunction (alpha s) = T - s.val ^ 2) ∧
      alpha ⟨0, ⟨le_rfl, Real.sqrt_nonneg tau⟩⟩ = x ∧
      alpha ⟨Real.sqrt tau, ⟨Real.sqrt_nonneg tau, le_rfl⟩⟩ = y := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  have hmem (k : ℕ) (s : Icc 0 (Real.sqrt tau)) : s.val ^ 2 ∈ Icc 0 tau :=
    M14.squarePath_parameter_mem (p k)
      (by simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using s.property)
  obtain ⟨alpha, phi, hphi, hlim⟩ := uniform_subsequence_of_compact_range
    (fun k (s : Icc 0 (Real.sqrt tau)) => (p k).curve (s.val ^ 2))
    (backward_squarePaths_equicontinuous p hD henergy) hK
    (fun k s => hpaths k (hmem k s))
  refine ⟨alpha, phi, hphi, hlim, ?_, ?_, ?_, ?_⟩
  · intro s
    exact hK.isClosed.mem_of_tendsto (hlim.tendsto_at s)
      (Eventually.of_forall (fun k => hpaths (phi k) (hmem (phi k) s)))
  · intro s
    have htime : Continuous (fun q : G.Point => G.spacetime.timeFunction q) :=
      (show ContMDiff (spacetimeModel 3) 𝓘(ℝ) ∞
        (fun q : G.Point => G.spacetime.timeFunction q) from G.spacetime.time_smooth).continuous
    have ht := htime.continuousAt.tendsto.comp (hlim.tendsto_at s)
    have hconst : Tendsto (fun k => G.spacetime.timeFunction ((p (phi k)).curve (s.val ^ 2)))
        atTop (𝓝 (T - s.val ^ 2)) := by
      convert tendsto_const_nhds (x := T - s.val ^ 2) using 1
      funext k
      exact (p (phi k)).curve_time _ (hmem (phi k) s)
    exact tendsto_nhds_unique ht hconst
  · have ht := hlim.tendsto_at ⟨0, ⟨le_rfl, Real.sqrt_nonneg tau⟩⟩
    have hconst : Tendsto (fun k => (p (phi k)).curve ((0 : ℝ) ^ 2)) atTop (𝓝 x) := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0), M14BackwardPath.curve_start]
        using (tendsto_const_nhds (x := x) : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
    exact tendsto_nhds_unique ht hconst
  · have ht := hlim.tendsto_at ⟨Real.sqrt tau, ⟨Real.sqrt_nonneg tau, le_rfl⟩⟩
    have hconst : Tendsto (fun k => (p (phi k)).curve (Real.sqrt tau ^ 2)) atTop (𝓝 y) := by
      simpa only [Real.sq_sqrt (p 0).tau_lt.le, M14BackwardPath.curve_end]
        using (tendsto_const_nhds (x := y) : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
    exact tendsto_nhds_unique ht hconst

end PoincareConjecture.Proofs.M46
