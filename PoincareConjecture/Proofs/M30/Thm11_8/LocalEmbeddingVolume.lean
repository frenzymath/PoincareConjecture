import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.RiemannianMetric



theorem volumeMeasure_ball_le_of_local_tangent_comparison
    {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] [T3Space M] [T3Space N]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N) (p : M) {r R C : ℝ}
    (_hr : 0 < r) (hR : 0 < R) (hC : 0 < C) (hCr : C * r < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hsource : closure (g.ball p R) ⊆ e.source)
    (he : ∀ x ∈ e.source, ContMDiffAt (𝓡 n) (𝓡 n) 1 e x)
    (hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 n) (𝓡 n) 1 e.symm y)
    (hbound : ∀ x ∈ closure (g.ball p R), ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * g.tangentNorm x v ∧
      g.tangentNorm x v ≤ C * h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)) :
    h.volumeMeasure (h.ball (e p) r) ≤
      ENNReal.ofReal C ^ n * g.volumeMeasure (g.ball p (C * r)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hball (a : ℝ) : IsOpen (g.ball p a) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hed : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨fun x hx => (he x hx).mdifferentiableAt (by norm_num) |>.mdifferentiableWithinAt,
      fun y hy => (hei y hy).mdifferentiableAt (by norm_num) |>.mdifferentiableWithinAt⟩
  have hinv := g.inverse_tangentNorm_le_of_le h e hed hsource
    (fun x hx v => (hbound x hx v).2)
  have hcover := g.ball_subset_image_ball_of_inverse_tangentNorm_le h e p
    hR hC hCr hcompact hsource hei hinv
  have hsmall : g.ball p (C * r) ⊆ g.ball p R :=
    fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hCr.le)
  apply (measure_mono hcover).trans
  exact g.volumeMeasure_image_le_of_tangentNorm_le h e (hball R)
    (subset_closure.trans hsource)
    (fun x hx => (he x hx).contMDiffWithinAt) hC
    (fun x hx v => (hbound x (subset_closure hx) v).1)
    (hball (C * r)).measurableSet hsmall




theorem ball_volume_lower_bound_of_local_tangent_comparisons
    {n : ℕ} {M : Type u} {N : ℕ → Type v}
    [TopologicalSpace M] [∀ k, TopologicalSpace (N k)]
    [T3Space M] [∀ k, T3Space (N k)]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [∀ k, MeasurableSpace (N k)] [∀ k, BorelSpace (N k)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (N k)]
    [∀ k, IsManifold (𝓡 n) ∞ (N k)]
    (g : RiemannianMetric n M) (h : ∀ k, RiemannianMetric n (N k))
    (e : ∀ k, OpenPartialHomeomorph M (N k))
    (hcomplete : MetricComplete g) (p : M) {r : ℝ} (hr : 0 < r) (kappa : ℝ)
    (he : ∀ k x, x ∈ (e k).source → ContMDiffAt (𝓡 n) (𝓡 n) 1 (e k) x)
    (hei : ∀ k y, y ∈ (e k).target → ContMDiffAt (𝓡 n) (𝓡 n) 1 (e k).symm y)
    (hcomparison : ∀ K : Set M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ k in atTop,
      K ⊆ (e k).source ∧ ∀ x ∈ K, ∀ v : TangentSpace (𝓡 n) x,
        (h k).tangentNorm (e k x) (mfderiv (𝓡 n) (𝓡 n) (e k) x v) ≤
          C * g.tangentNorm x v ∧
        g.tangentNorm x v ≤
          C * (h k).tangentNorm (e k x) (mfderiv (𝓡 n) (𝓡 n) (e k) x v))
    (hvolume : ∀ rho : ℝ, 0 < rho → rho < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (kappa * rho ^ n) ≤
        (h k).volumeMeasure ((h k).ball (e k p) rho)) :
    ENNReal.ofReal (kappa * r ^ n) ≤ g.volumeMeasure (g.ball p r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hsmall (rho : ℝ) (hrho : 0 < rho) (hrhor : rho < r) :
      ENNReal.ofReal (kappa * rho ^ n) ≤ g.volumeMeasure (g.ball p r) := by
    have hdistortion (C : ℝ) (hC : 1 < C) (hCr : C * rho < r) :
        ENNReal.ofReal (kappa * rho ^ n) ≤
          ENNReal.ofReal C ^ n * g.volumeMeasure (g.ball p r) := by
      let R := C * rho + 1
      have hCp : 0 < C := zero_lt_one.trans hC
      have hR : 0 < R := by dsimp only [R]; positivity
      have hclosed : IsClosed {x : M | g.edist p x ≤ ENNReal.ofReal R} :=
        isClosed_le (continuous_const.edist continuous_id) continuous_const
      have hcompact : IsCompact (closure (g.ball p R)) :=
        (g.isCompact_closedBall_of_metricComplete hcomplete p R).of_isClosed_subset
          isClosed_closure (closure_minimal
            (fun y hy => (show g.edist p y < ENNReal.ofReal R from hy).le) hclosed)
      obtain ⟨k, hk, hv⟩ :=
        ((hcomparison _ hcompact C hC).and (hvolume rho hrho hrhor)).exists
      have hupper := g.volumeMeasure_ball_le_of_local_tangent_comparison
        (h k) (e k) p hrho hR hCp (by dsimp only [R]; linarith)
        hcompact hk.1 (he k) (hei k) hk.2
      have hsub : g.ball p (C * rho) ⊆ g.ball p r :=
        fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hCr.le)
      exact hv.trans (hupper.trans (mul_le_mul' le_rfl (measure_mono hsub)))
    have hpower : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n) (𝓝 1) (𝓝 1) := by
      simpa only [Function.comp_def, ENNReal.ofReal_one, one_pow] using
        ((ENNReal.continuous_pow n).comp ENNReal.continuous_ofReal).tendsto 1
    have hlimit : Tendsto
        (fun C : ℝ => ENNReal.ofReal C ^ n * g.volumeMeasure (g.ball p r))
        (𝓝[>] 1) (𝓝 (g.volumeMeasure (g.ball p r))) := by
      have h := ENNReal.Tendsto.mul hpower (Or.inl one_ne_zero)
        (tendsto_const_nhds (x := g.volumeMeasure (g.ball p r)))
        (Or.inr ENNReal.one_ne_top)
      simpa only [one_mul] using h.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlimit
    have hCr : ∀ᶠ C : ℝ in 𝓝 1, C * rho < r :=
      (continuous_id.mul continuous_const).continuousAt.eventually_lt_const
        (by change 1 * rho < r; simpa only [one_mul] using hrhor)
    filter_upwards [self_mem_nhdsWithin, hCr.filter_mono nhdsWithin_le_nhds]
      with C hC hCr'
    exact hdistortion C hC hCr'
  have hradius : Tendsto (fun rho : ℝ => ENNReal.ofReal (kappa * rho ^ n))
      (𝓝 r) (𝓝 (ENNReal.ofReal (kappa * r ^ n))) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow n))).tendsto r
  apply le_of_tendsto (x := 𝓝[<] r) (hradius.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds] with rho hrhor hrho
  exact hsmall rho hrho hrhor

end PoincareConjecture.RiemannianMetric
