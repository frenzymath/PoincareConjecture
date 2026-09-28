import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Backward
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology

theorem PoincareConjecture.RiemannianMetric.exists_openFiber_normalizedGradient_curve_ending_at
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M)
    (hc : PoincareConjecture.MetricComplete g)
    {f : M → Fin k → ℝ} {φ : M → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (p : M) {l H r R T : ℝ}
    (hl : 0 < l) (hH : 0 ≤ H) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hroom : r + T / l ≤ R)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal R → y ∈ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    let DL := gL.leviCivitaData
    let φL := φ ∘ incl
    (∀ y : openFiber f U c, l ≤ gL.tangentNorm y (DL.gradient φL y)) →
    (∀ y : openFiber f U c, ∀ v : TangentSpace (𝓡 m) y,
      mvfderiv (𝓡 m) φL y v = 0 →
        DL.hessian φL y v v ≤ H * gL.inner y v v) →
    ∀ x : openFiber f U c, g.edist p (incl x) ≤ ENNReal.ofReal r →
      ∃ (ε : ℝ) (γ : ℝ → openFiber f U c), 0 < ε ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 m) ∞ γ (Ioo (-ε) (T + ε)) ∧
        γ T = x ∧
        IsMIntegralCurveOn (I := 𝓡 m) γ (DL.normalizedGradient φL)
          (Ioo (-ε) (T + ε)) ∧
        ∀ t ∈ Icc 0 T,
          φ (incl (γ t)) = φ (incl x) - T + t ∧
          gL.edist (γ t) x ≤ ENNReal.ofReal ((T - t) / l) ∧
          g.edist p (incl (γ t)) ≤ ENNReal.ofReal (r + (T - t) / l) := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  let DL := gL.leviCivitaData
  let φL := φ ∘ incl
  dsimp only
  intro hgrad hhess x hx
  have hincl : ContMDiff (𝓡 m) (𝓡 (m + k)) ∞ incl :=
    contMDiff_openFiberIncl (m := m) hf U hreg c
  have hφL : ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) ∞ φL := hφ.comp hincl
  have hdist (y z : openFiber f U c) :
      g.edist (incl y) (incl z) ≤ gL.edist y z :=
    edist_map_le_of_metric_pullback gL g hincl
      (openRegularFiberMetric_inner hf U hreg c g) y z
  let K : Set (openFiber f U c) := {y | g.edist p (incl y) ≤ ENNReal.ofReal R}
  have hK : IsCompact K := by
    apply (isEmbedding_openFiberIncl f U c).isCompact_iff.mpr
    have he : incl '' K = {y | g.edist p y ≤ ENNReal.ofReal R} ∩ f ⁻¹' {c} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.2⟩
      · rintro ⟨hy, hfy⟩
        exact ⟨⟨⟨y, hball y hy⟩, hfy⟩, hy, rfl⟩
    rw [show openFiberIncl f U c '' K = incl '' K from rfl, he]
    exact (g.isCompact_closedBall_of_metricComplete hc p R).inter_right
      (isClosed_singleton.preimage hf.continuous)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : openFiber f U c → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : openFiber f U c → Type _) :=
    ⟨⟨gL.inner, gL.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (openFiber f U c) :=
    EMetricSpace.ofRiemannianMetric (𝓡 m) (openFiber f U c)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hTdiv : 0 ≤ T / l := div_nonneg hT hl.le
  have hcompact : IsCompact {y | gL.edist x y ≤ ENNReal.ofReal (T / l)} := by
    apply hK.of_isClosed_subset
      (show IsClosed {y | EDist.edist x y ≤ ENNReal.ofReal (T / l)} from
        isClosed_le (continuous_const.edist continuous_id) continuous_const)
    intro y hy
    change g.edist p (incl y) ≤ ENNReal.ofReal R
    have htri : g.edist p (incl y) ≤ g.edist p (incl x) + g.edist (incl x) (incl y) :=
      Manifold.riemannianEDist_triangle
    apply (htri.trans (add_le_add hx ((hdist x y).trans hy))).trans
    rw [← ENNReal.ofReal_add hr hTdiv]
    exact ENNReal.ofReal_le_ofReal hroom
  obtain ⟨ε, γ, hε, hs, hend, _, ho, hb⟩ :=
    DL.exists_normalizedGradient_curve_ending_at_of_isCompact_closedBall
      isOpen_univ hφL.contMDiffOn hl hH (fun y _ => hgrad y)
      (fun y _ => hhess y) x hTdiv hT le_rfl hcompact (subset_univ _)
  refine ⟨ε, γ, hε, hs, hend, ho, ?_⟩
  intro t ht
  obtain ⟨hlevel, hlen⟩ := hb t ht
  refine ⟨hlevel, hlen, ?_⟩
  have htri : g.edist p (incl (γ t)) ≤
      g.edist p (incl x) + g.edist (incl x) (incl (γ t)) :=
    Manifold.riemannianEDist_triangle
  have hsym : gL.edist x (γ t) = gL.edist (γ t) x :=
    Manifold.riemannianEDist_comm
  have hlen' : g.edist (incl x) (incl (γ t)) ≤ ENNReal.ofReal ((T - t) / l) := by
    apply (hdist x (γ t)).trans
    rwa [hsym]
  apply (htri.trans (add_le_add hx hlen')).trans
  rw [← ENNReal.ofReal_add hr (div_nonneg (sub_nonneg.mpr ht.2) hl.le)]

theorem PoincareConjecture.RiemannianMetric.exists_uniform_openFiber_normalizedGradient_manifoldFlow
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M)
    (hc : PoincareConjecture.MetricComplete g)
    {f : M → Fin k → ℝ} {φ : M → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (p : M) {l H r R T : ℝ}
    (hl : 0 < l) (hH : 0 ≤ H) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hroom : r + T / l ≤ R)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal R → y ∈ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    let DL := gL.leviCivitaData
    let φL := φ ∘ incl
    (∀ y : openFiber f U c, l ≤ gL.tangentNorm y (DL.gradient φL y)) →
    (∀ y : openFiber f U c, ∀ v : TangentSpace (𝓡 m) y,
      mvfderiv (𝓡 m) φL y v = 0 →
        DL.hessian φL y v v ≤ H * gL.inner y v v) →
    ∃ (V : Set (openFiber f U c)) (δ : ℝ)
      (Φ : ℝ × openFiber f U c → openFiber f U c),
      IsOpen V ∧ {y | g.edist p (incl y) ≤ ENNReal.ofReal r} ⊆ V ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 m)) (𝓡 m) ∞ Φ
        (Ioo (-δ) (T + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, IsMIntegralCurveOn (I := 𝓡 m) (fun t => Φ (t, y))
        (DL.normalizedGradient φL) (Ioo (-δ) (T + δ))) ∧
      (∀ y ∈ V, ∀ t ∈ Icc 0 T,
        φ (incl (Φ (t, y))) = φ (incl y) + t ∧
        gL.edist y (Φ (t, y)) ≤ ENNReal.ofReal (t / l) ∧
        ∀ v : TangentSpace (𝓡 m) y, mvfderiv (𝓡 m) φL y v = 0 →
          gL.inner (Φ (t, y)) (mfderiv (𝓡 m) (𝓡 m) (fun z => Φ (t, z)) y v)
            (mfderiv (𝓡 m) (𝓡 m) (fun z => Φ (t, z)) y v) ≤
          gL.inner y v v * Real.exp (2 * (H / l ^ 2) * t)) ∧
      ∀ y : openFiber f U c, g.edist p (incl y) ≤ ENNReal.ofReal r →
        ∀ t ∈ Icc 0 T,
          g.edist p (incl (Φ (t, y))) ≤ ENNReal.ofReal (r + t / l) := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  let DL := gL.leviCivitaData
  let φL := φ ∘ incl
  dsimp only
  intro hgrad hhess
  have hincl : ContMDiff (𝓡 m) (𝓡 (m + k)) ∞ incl :=
    contMDiff_openFiberIncl (m := m) hf U hreg c
  have hφL : ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) ∞ φL := hφ.comp hincl
  have hdist (y z : openFiber f U c) :
      g.edist (incl y) (incl z) ≤ gL.edist y z :=
    edist_map_le_of_metric_pullback gL g hincl
      (openRegularFiberMetric_inner hf U hreg c g) y z
  let K : Set (openFiber f U c) := {y | g.edist p (incl y) ≤ ENNReal.ofReal r}
  let S : Set (openFiber f U c) := {y | g.edist p (incl y) ≤ ENNReal.ofReal R}
  have hcompact (a : ℝ) (ha : a ≤ R) :
      IsCompact {y : openFiber f U c | g.edist p (incl y) ≤ ENNReal.ofReal a} := by
    apply (isEmbedding_openFiberIncl f U c).isCompact_iff.mpr
    have he : incl '' {y | g.edist p (incl y) ≤ ENNReal.ofReal a} =
        {y | g.edist p y ≤ ENNReal.ofReal a} ∩ f ⁻¹' {c} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.2⟩
      · rintro ⟨hy, hfy⟩
        exact ⟨⟨⟨y, hball y (hy.trans (ENNReal.ofReal_le_ofReal ha))⟩, hfy⟩, hy, rfl⟩
    change IsCompact (incl '' {y | g.edist p (incl y) ≤ ENNReal.ofReal a})
    rw [he]
    exact (g.isCompact_closedBall_of_metricComplete hc p a).inter_right
      (isClosed_singleton.preimage hf.continuous)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hTdiv : 0 ≤ T / l := div_nonneg hT hl.le
  have hrR : r ≤ R := by linarith
  have hbuffer : ∀ x ∈ K, ∀ y, gL.edist x y ≤ ENNReal.ofReal (T / l) → y ∈ S := by
    intro x hx y hy
    have htri : g.edist p (incl y) ≤
        g.edist p (incl x) + g.edist (incl x) (incl y) :=
      Manifold.riemannianEDist_triangle
    apply (htri.trans (add_le_add hx ((hdist x y).trans hy))).trans
    rw [← ENNReal.ofReal_add hr hTdiv]
    exact ENNReal.ofReal_le_ofReal hroom
  obtain ⟨V, δ, Φ, hV, hKV, _, hδ, hs, hi, ho, hb⟩ :=
    DL.exists_uniform_normalizedGradient_manifoldFlow_on_compact_buffer isOpen_univ
      hφL.contMDiffOn hl hH (fun y _ => hgrad y) (fun y _ => hhess y)
      (hcompact r hrR) (hcompact R le_rfl)
      (fun y hy => hy.trans (ENNReal.ofReal_le_ofReal hrR)) (subset_univ _) hT hbuffer
  refine ⟨V, δ, Φ, hV, hKV, hδ, hs, hi, fun y hy => (ho y hy).2, hb, ?_⟩
  intro y hy t ht
  have htri : g.edist p (incl (Φ (t, y))) ≤
      g.edist p (incl y) + g.edist (incl y) (incl (Φ (t, y))) :=
    Manifold.riemannianEDist_triangle
  apply (htri.trans (add_le_add hy
    ((hdist y (Φ (t, y))).trans (hb y (hKV hy) t ht).2.1))).trans
  rw [← ENNReal.ofReal_add hr (div_nonneg ht.1 hl.le)]
