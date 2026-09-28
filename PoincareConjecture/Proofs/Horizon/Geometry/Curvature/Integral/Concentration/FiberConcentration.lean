import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.FiberAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedAnnularConcentration

open Set Filter MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.RiemannianMetric

private theorem integrableOn_openFiber_ambient_ball_of_continuous
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M] [IsManifold (𝓡 (m+k)) ∞ M]
    (g : RiemannianMetric (m+k) M) (hc : MetricComplete g)
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (p : M) {r R : ℝ} (hrR : r ≤ R)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal R → y ∈ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let gL := g.openRegularFiberMetric hf U hreg c
    ∀ H : openFiber f U c → ℝ, Continuous H →
      IntegrableOn H (openFiberIncl f U c ⁻¹' g.ball p r) gL.volumeMeasure := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openFiberChartedSpace (m := m) hf U hreg c
  letI := isManifold_openFiber (m := m) hf U hreg c
  dsimp only
  intro H hH
  apply (hH.continuousOn.integrableOn_compact
    (g.isCompact_openFiber_preimage_closedBall hc hf.continuous U c p R hball)).mono_set
  intro x hx
  exact (show g.edist p (openFiberIncl f U c x) < ENNReal.ofReal r from hx).le.trans
    (ENNReal.ofReal_le_ofReal hrR)

theorem exists_subseq_openFiber_critical_ambient_ball_weighted_scalar_integral_tendsto_atTop
    {m k : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) (M j)]
    [∀ j, IsManifold (𝓡 (m+k)) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ∀ j, RiemannianMetric (m+k) (M j))
    (hc : ∀ j, MetricComplete (g j))
    (f : ∀ j, M j → Fin k → ℝ)
    (hf : ∀ j, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ (f j))
    (U : ∀ j, TopologicalSpace.Opens (M j))
    (hreg : ∀ j x, x ∈ U j → Function.Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) (f j) x))
    (c : ℕ → Fin k → ℝ) (hm : 0 < m) {d : ℕ} (hd : 1 ≤ d) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin m))
        (openFiber (f j) (U j) (c j)) :=
      fun j => openFiberChartedSpace (m := m) (hf j) (U j) (hreg j) (c j)
    letI : ∀ j, IsManifold (𝓡 m) ∞ (openFiber (f j) (U j) (c j)) :=
      fun j => isManifold_openFiber (m := m) (hf j) (U j) (hreg j) (c j)
    let incl := fun j => openFiberIncl (f j) (U j) (c j)
    let gL := fun j => (g j).openRegularFiberMetric (hf j) (U j) (hreg j) (c j)
    ∀ (D : ∀ j, LeviCivitaData (gL j))
      (p : ∀ j, openFiber (f j) (U j) (c j))
      (o : ∀ j, κ → openFiber (f j) (U j) (c j))
      (s C₀ D₀ : κ → ℝ)
      (q : ∀ j, ι → openFiber (f j) (U j) (c j))
      (a : ℕ → ι → ℝ) (r₀ R C : ι → ℝ)
      (W : ∀ j, Set (openFiber (f j) (U j) (c j)))
      (K : ∀ j, openFiber (f j) (U j) (c j) → ℝ),
    (∀ j x (v w : TangentSpace (𝓡 m) x),
      -(K j x) ≤ (D j).sectionalCurvature x v w) →
    (∀ j, MeasurableSet (W j)) →
    (∀ j, IntegrableOn (K j) (W j) (gL j).volumeMeasure) →
    (∀ j x, 0 ≤ K j x) →
    (∀ j i, 0 ≤ a j i) →
    (∀ i, 0 < r₀ i) → (∀ i, 0 ≤ R i) → (∀ i, R i < 19*r₀ i/16) →
    (∀ i, 0 ≤ C i) → (∀ i, 0 ≤ D₀ i) → (∀ i, 0 ≤ s i) →
    (∀ j y, (g j).edist (incl j (p j)) y ≤ ENNReal.ofReal 1 → y ∈ U j) →
    (∀ j i y, (g j).edist (incl j (o j i)) y ≤ ENNReal.ofReal (3*s i) → y ∈ U j) →
    (∀ j i y, (g j).edist (incl j (q j i)) y ≤ ENNReal.ofReal (3*r₀ i) → y ∈ U j) →
    (∀ j i y, (g j).edist (incl j (q j i)) y ≤ ENNReal.ofReal (8*a j i) → y ∈ U j) →
    (∀ j i, {x | ((g j).edist (incl j (o j i)) (incl j x)).toReal ∈ Icc (s i/2) (3*s i)} ⊆ W j) →
    (∀ j i, {x | ((g j).edist (incl j (q j i)) (incl j x)).toReal ≤ 3*r₀ i} ⊆ W j) →
    (∀ j i, incl j ⁻¹' (g j).ball (incl j (q j i)) (8*a j i) ⊆ W j) →
    (∀ᶠ j in atTop,
      (incl j ⁻¹' (g j).ball (incl j (p j)) 1 ⊆
        (⋃ i, {x | ((g j).edist (incl j (o j i)) (incl j x)).toReal ∈
          Icc (113*s i/96) (19*s i/16)}) ∪
            ⋃ i, incl j ⁻¹' (g j).ball (incl j (q j i)) (R i)) ∧
      (∀ i, (∫ x in {x | ((g j).edist (incl j (o j i)) (incl j x)).toReal ∈
          Icc (113*s i/96) (19*s i/16)}, max 0 ((D j).scalarCurvature x) ∂(gL j).volumeMeasure) ≤
        C₀ i + D₀ i * ∫ x in {x | ((g j).edist (incl j (o j i)) (incl j x)).toReal ∈
          Icc (s i/2) (3*s i)}, K j x ∂(gL j).volumeMeasure) ∧
      (∀ i r, 0 < r → 2*a j i ≤ r → r ≤ r₀ i →
        (∫ x in {x | ((g j).edist (incl j (q j i)) (incl j x)).toReal ∈
          Icc (113*r/96) (19*r/16)}, max 0 ((D j).scalarCurvature x) ∂(gL j).volumeMeasure) ≤
        C i * (r^d + ∫ x in {x | ((g j).edist (incl j (q j i)) (incl j x)).toReal ∈
          Icc (r/2) (3*r)}, K j x ∂(gL j).volumeMeasure))) →
    Tendsto (fun j =>
      (∫ x in incl j ⁻¹' (g j).ball (incl j (p j)) 1,
        max 0 ((D j).scalarCurvature x) ∂(gL j).volumeMeasure) /
      (1 + ∫ x in W j, K j x ∂(gL j).volumeMeasure)) atTop atTop →
    ∃ i : ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ j, 0 < a (φ j) i) ∧
      Tendsto (fun j =>
        (∫ x in incl (φ j) ⁻¹' (g (φ j)).ball (incl (φ j) (q (φ j) i)) (4*a (φ j) i),
          max 0 ((D (φ j)).scalarCurvature x) ∂(gL (φ j)).volumeMeasure) /
        (1 + ∫ x in incl (φ j) ⁻¹' (g (φ j)).ball (incl (φ j) (q (φ j) i)) (8*a (φ j) i),
          K (φ j) x ∂(gL (φ j)).volumeMeasure)) atTop atTop ∧
      Tendsto (fun j =>
        (∫ x in incl (φ j) ⁻¹' (g (φ j)).ball (incl (φ j) (q (φ j) i)) (4*a (φ j) i),
          (D (φ j)).scalarCurvature x ∂(gL (φ j)).volumeMeasure) /
        (1 + ∫ x in incl (φ j) ⁻¹' (g (φ j)).ball (incl (φ j) (q (φ j) i)) (8*a (φ j) i),
          K (φ j) x ∂(gL (φ j)).volumeMeasure)) atTop atTop := by
  classical
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin m))
      (openFiber (f j) (U j) (c j)) :=
    fun j => openFiberChartedSpace (m := m) (hf j) (U j) (hreg j) (c j)
  letI : ∀ j, IsManifold (𝓡 m) ∞ (openFiber (f j) (U j) (c j)) :=
    fun j => isManifold_openFiber (m := m) (hf j) (U j) (hreg j) (c j)
  let incl := fun j => openFiberIncl (f j) (U j) (c j)
  let gL := fun j => (g j).openRegularFiberMetric (hf j) (U j) (hreg j) (c j)
  dsimp only
  intro D p o s C₀ D₀ q a r₀ R C W K hsec hW hKi hKn ha hr₀ hRn hR hC hD₀ hs
    hMainBall hOrdBall hCritBall hDoubleBall hOrdBuffer hCritBuffer hDoubleBuffer hevent hlarge
  letI : ∀ j, ConnectedSpace (M j) := fun j => { toNonempty := ⟨incl j (p j)⟩ }
  letI : ∀ j, MetricSpace (M j) := fun j => (g j).toMetricSpace
  obtain ⟨L, _, hL⟩ := Poincare.CurvatureIntegral.exists_buffered_annulus_overlap
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hevent
  let A := (∑ i, C₀ i) + ∑ i, C i * r₀ i ^ d / (1 - (227 / 228 : ℝ) ^ d)
  let B := (∑ i, D₀ i) + (L : ℝ) * ∑ i, C i
  let μ := fun j => (gL (j+J)).volumeMeasure
  let E₀ := fun j => incl (j+J) ⁻¹' (g (j+J)).ball (incl (j+J) (p (j+J))) 1
  let V := fun j i => incl (j+J) ⁻¹' (g (j+J)).ball (incl (j+J) (q (j+J) i)) (4*a (j+J) i)
  let E := fun j i => incl (j+J) ⁻¹' (g (j+J)).ball (incl (j+J) (q (j+J) i)) (8*a (j+J) i)
  let h := fun j x => max 0 ((D (j+J)).scalarCurvature x)
  let b := fun j => 1 + ∫ x in W (j+J), K (j+J) x ∂μ j
  let w := fun j i => 1 + ∫ x in E j i, K (j+J) x ∂μ j
  have hmeas (j : ℕ) (x : openFiber (f j) (U j) (c j)) (r : ℝ) :
      MeasurableSet (incl j ⁻¹' (g j).ball (incl j x) r) := by
    rw [← (g j).toMetricSpace_ball]
    exact (Metric.isOpen_ball.preimage
      (isEmbedding_openFiberIncl (f j) (U j) (c j)).continuous).measurableSet
  have hiMain (j : ℕ) : IntegrableOn (fun x => max 0 ((D j).scalarCurvature x))
      (incl j ⁻¹' (g j).ball (incl j (p j)) 1) (gL j).volumeMeasure :=
    integrableOn_openFiber_ambient_ball_of_continuous (g j) (hc j) (hf j) (U j)
      (hreg j) (c j) (incl j (p j)) le_rfl (hMainBall j) _
      (continuous_const.max (D j).continuous_scalarCurvature)
  have hiCrit (j : ℕ) (i : ι) : IntegrableOn (D j).scalarCurvature
      (incl j ⁻¹' (g j).ball (incl j (q j i)) (4*a j i)) (gL j).volumeMeasure :=
    integrableOn_openFiber_ambient_ball_of_continuous (g j) (hc j) (hf j) (U j)
      (hreg j) (c j) (incl j (q j i)) (by nlinarith only [ha j i])
      (hDoubleBall j i) _ (D j).continuous_scalarCurvature
  have hb (j : ℕ) : 0 < b j := by
    have hnK : 0 ≤ ∫ x in W (j+J), K (j+J) x ∂μ j := integral_nonneg (hKn _)
    dsimp [b]
    linarith
  have hw (j : ℕ) (i : ι) : 0 < w j i := by
    have hnK : 0 ≤ ∫ x in E j i, K (j+J) x ∂μ j := integral_nonneg (hKn _)
    dsimp [w]
    linarith
  have hwb (j : ℕ) (i : ι) : w j i ≤ b j := by
    apply add_le_add_right
    exact setIntegral_mono_set (hKi _) (Filter.Eventually.of_forall (hKn _))
      (Filter.Eventually.of_forall (hDoubleBuffer _ i))
  have houtside (j : ℕ) :
      (∫ x in E₀ j \ ⋃ i, V j i, h j x ∂μ j) ≤ (|A| + |B|) * b j := by
    obtain ⟨hcov, hord, hcrit⟩ := hJ (j+J) (by omega)
    have hmix := (g (j+J)).integral_openFiber_pos_scalar_outside_iUnion_ambient_ball_le_of_weighted_mixed_annuli
      (hc _) (hf _) (U _) (hreg _) (c _) (p _) (D _)
      (o _) s C₀ D₀ (q _) (a _) r₀ R C hm hs hRn
      (hMainBall _) (hOrdBall _) (hCritBall _) (ha _) hr₀ hR hC hd
      (hW _) (hKi _) (hKn _) hL hD₀ (hOrdBuffer _) (hCritBuffer _)
      hcov hord hcrit
    change (∫ x in E₀ j \ ⋃ i, V j i, h j x ∂μ j) ≤
      A + B * ∫ x in W (j+J), K (j+J) x ∂μ j at hmix
    have hI : 0 ≤ ∫ x in W (j+J), K (j+J) x ∂μ j := integral_nonneg (hKn _)
    apply hmix.trans
    dsimp [b]
    have hBA := mul_le_mul_of_nonneg_right (le_abs_self B) hI
    have hpos := mul_nonneg (abs_nonneg A) hI
    nlinarith [le_abs_self A, abs_nonneg B]
  have hlarge' : ∀ T : ℝ, ∃ j, T < (∫ x in E₀ j, h j x ∂μ j) / b j := by
    intro T
    exact ((hlarge.comp (tendsto_add_atTop_nat J)).eventually (eventually_gt_atTop T)).exists
  obtain ⟨i, φ, hφ, hdiv⟩ :=
    Poincare.CurvatureIntegral.exists_subseq_fixed_member_integral_ratio_tendsto_atTop
      μ E₀ V h (fun j => hmeas _ _ _) (fun j i => hmeas _ _ _)
      (fun _ _ => le_max_left _ _) (fun j => hiMain (j+J))
      (fun j i => by
        simpa only [h, V, μ, IntegrableOn, max_comm] using (hiCrit (j+J) i).pos_part)
      b hb w hw hwb (|A| + |B|) houtside hlarge'
  obtain ⟨J', hJ'⟩ := eventually_atTop.mp (hdiv.eventually (eventually_gt_atTop 0))
  let ψ := fun j => φ (j+J')+J
  have hψ : StrictMono ψ := fun x y hxy =>
    Nat.add_lt_add_right (hφ (Nat.add_lt_add_right hxy J')) J
  have hpos (j : ℕ) : 0 < a (ψ j) i := by
    by_contra hnpos
    have haz : a (ψ j) i = 0 := le_antisymm (le_of_not_gt hnpos) (ha _ _)
    have hball : V (φ (j+J')) i = ∅ := by
      dsimp [V]
      change incl (ψ j) ⁻¹' (g (ψ j)).ball (incl (ψ j) (q (ψ j) i)) (4*a (ψ j) i) = ∅
      rw [haz,mul_zero,← (g (ψ j)).toMetricSpace_ball,Metric.ball_zero,preimage_empty]
    have ht := hJ' (j+J') (by omega)
    rw [hball,setIntegral_empty,zero_div] at ht
    exact (lt_irrefl 0) ht
  have hposdiv : Tendsto (fun j =>
      (∫ x in incl (ψ j) ⁻¹' (g (ψ j)).ball (incl (ψ j) (q (ψ j) i)) (4*a (ψ j) i),
        max 0 ((D (ψ j)).scalarCurvature x) ∂(gL (ψ j)).volumeMeasure) /
      (1 + ∫ x in incl (ψ j) ⁻¹' (g (ψ j)).ball (incl (ψ j) (q (ψ j) i)) (8*a (ψ j) i),
        K (ψ j) x ∂(gL (ψ j)).volumeMeasure)) atTop atTop :=
    hdiv.comp (tendsto_add_atTop_nat J')
  refine ⟨i,ψ,hψ,hpos,hposdiv,?_⟩
  apply tendsto_atTop.2
  intro T
  filter_upwards [(tendsto_atTop.1 hposdiv) (T+(m:ℝ)^2)] with j hj
  have hsub : incl (ψ j) ⁻¹' (g (ψ j)).ball (incl (ψ j) (q (ψ j) i)) (4*a (ψ j) i) ⊆
      incl (ψ j) ⁻¹' (g (ψ j)).ball (incl (ψ j) (q (ψ j) i)) (8*a (ψ j) i) := by
    apply preimage_mono
    rw [← (g (ψ j)).toMetricSpace_ball,← (g (ψ j)).toMetricSpace_ball]
    exact Metric.ball_subset_ball (by nlinarith only [ha (ψ j) i])
  have hcorr := (D (ψ j)).normalized_integral_scalarCurvature_posPart_le_add_of_subset
    (hmeas _ _ _) hsub (hKn _) (fun x _ => hsec _ x) (hiCrit (ψ j) i)
    ((hKi _).mono_set (hDoubleBuffer _ i))
  linarith

end PoincareConjecture.RiemannianMetric
