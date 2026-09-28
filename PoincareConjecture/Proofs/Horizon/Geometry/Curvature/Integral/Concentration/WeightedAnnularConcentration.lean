import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedFiniteCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

theorem normalized_integral_scalarCurvature_posPart_le_add_of_subset
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {s t : Set M} (hs : MeasurableSet s) (hst : s ⊆ t) {K : M → ℝ}
    (hK : ∀ x, 0 ≤ K x)
    (hsec : ∀ x ∈ s, ∀ v w : TangentSpace (𝓡 n) x,
      -K x ≤ D.sectionalCurvature x v w)
    (hR : IntegrableOn D.scalarCurvature s g.volumeMeasure)
    (hKi : IntegrableOn K t g.volumeMeasure) :
    (∫ x in s, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) /
        (1 + ∫ x in t, K x ∂g.volumeMeasure) ≤
      (∫ x in s, D.scalarCurvature x ∂g.volumeMeasure) /
        (1 + ∫ x in t, K x ∂g.volumeMeasure) + (n : ℝ) ^ 2 := by
  have hI : 0 ≤ ∫ x in t, K x ∂g.volumeMeasure := integral_nonneg hK
  have hp : 0 < 1 + ∫ x in t, K x ∂g.volumeMeasure := by linarith
  have hb := D.integral_scalarCurvature_posPart_le_integral_add_weight hs
    (fun x _ => hK x) hsec hR (hKi.mono_set hst)
  have hi := setIntegral_mono_set hKi (Filter.Eventually.of_forall hK)
    (Filter.Eventually.of_forall hst)
  change (∫ x in s, K x ∂g.volumeMeasure) ≤ _ at hi
  have hc := mul_le_mul_of_nonneg_left hi (sq_nonneg (n : ℝ))
  apply (div_le_iff₀ hp).mpr
  rw [add_mul, div_mul_cancel₀ _ hp.ne']
  nlinarith [sq_nonneg (n : ℝ)]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture

theorem exists_subseq_critical_ball_weighted_scalar_integral_tendsto_atTop_of_mixed_annuli
    {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (p : ∀ j, M j) (o : ∀ j, κ → M j) (s C₀ D₀ : κ → ℝ)
    (q : ∀ j, ι → M j) (a : ℕ → ι → ℝ) (r₀ R C : ι → ℝ)
    (W : ∀ j, Set (M j)) (K : ∀ j, M j → ℝ)
    (hn : 0 < n) {m : ℕ} (hm : 1 ≤ m)
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 n) x),
      -(K j x) ≤ (D j).sectionalCurvature x v w)
    (hW : ∀ j, MeasurableSet (W j))
    (hKi : ∀ j, IntegrableOn (K j) (W j) (g j).volumeMeasure)
    (hKn : ∀ j x, 0 ≤ K j x)
    (ha : ∀ j i, 0 ≤ a j i)
    (hr₀ : ∀ i, 0 < r₀ i) (hR : ∀ i, R i < 19 * r₀ i / 16)
    (hC : ∀ i, 0 ≤ C i) (hD₀ : ∀ i, 0 ≤ D₀ i)
    (hOrdBuffer : ∀ j i,
      {x : M j | ((g j).edist (o j i) x).toReal ∈ Icc (s i / 2) (3 * s i)} ⊆ W j)
    (hCritBuffer : ∀ j i,
      {x : M j | ((g j).edist (q j i) x).toReal ≤ 3 * r₀ i} ⊆ W j)
    (hDoubleBuffer : ∀ j i, (g j).ball (q j i) (8 * a j i) ⊆ W j)
    (hevent : ∀ᶠ j in atTop,
      ((g j).ball (p j) 1 ⊆
        (⋃ i, {x : M j | ((g j).edist (o j i) x).toReal ∈
          Icc (113 * s i / 96) (19 * s i / 16)}) ∪
            ⋃ i, (g j).ball (q j i) (R i)) ∧
      (∀ i, (∫ x in {x : M j | ((g j).edist (o j i) x).toReal ∈
          Icc (113 * s i / 96) (19 * s i / 16)},
        max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C₀ i + D₀ i *
          ∫ x in {x : M j | ((g j).edist (o j i) x).toReal ∈
            Icc (s i / 2) (3 * s i)}, K j x ∂(g j).volumeMeasure) ∧
      (∀ i, ∀ r : ℝ, 0 < r → 2 * a j i ≤ r → r ≤ r₀ i →
        (∫ x in {x : M j | ((g j).edist (q j i) x).toReal ∈
            Icc (113 * r / 96) (19 * r / 16)},
          max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C i *
            (r ^ m + ∫ x in {x : M j | ((g j).edist (q j i) x).toReal ∈
              Icc (r / 2) (3 * r)}, K j x ∂(g j).volumeMeasure)))
    (hlarge : Tendsto (fun j =>
      (∫ x in (g j).ball (p j) 1, max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) /
        (1 + ∫ x in W j, K j x ∂(g j).volumeMeasure)) atTop atTop) :
    ∃ i : ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ j, 0 < a (φ j) i) ∧
      Tendsto (fun j =>
        (∫ x in (g (φ j)).ball (q (φ j) i) (4 * a (φ j) i),
          max 0 ((D (φ j)).scalarCurvature x) ∂(g (φ j)).volumeMeasure) /
            (1 + ∫ x in (g (φ j)).ball (q (φ j) i) (8 * a (φ j) i),
              K (φ j) x ∂(g (φ j)).volumeMeasure)) atTop atTop ∧
      Tendsto (fun j =>
        (∫ x in (g (φ j)).ball (q (φ j) i) (4 * a (φ j) i),
          (D (φ j)).scalarCurvature x ∂(g (φ j)).volumeMeasure) /
            (1 + ∫ x in (g (φ j)).ball (q (φ j) i) (8 * a (φ j) i),
              K (φ j) x ∂(g (φ j)).volumeMeasure)) atTop atTop := by
  classical
  let : ∀ j, ConnectedSpace (M j) := fun j => { toNonempty := ⟨p j⟩ }
  let : ∀ j, MetricSpace (M j) := fun j => (g j).toMetricSpace
  obtain ⟨L, _, hL⟩ := Poincare.CurvatureIntegral.exists_buffered_annulus_overlap
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hevent
  let A := (∑ i, C₀ i) + ∑ i, C i * r₀ i ^ m / (1 - (227 / 228 : ℝ) ^ m)
  let B := (∑ i, D₀ i) + (L : ℝ) * ∑ i, C i
  let μ := fun j => (g (j + J)).volumeMeasure
  let U := fun j => (g (j + J)).ball (p (j + J)) 1
  let V := fun j i => (g (j + J)).ball (q (j + J) i) (4 * a (j + J) i)
  let E := fun j i => (g (j + J)).ball (q (j + J) i) (8 * a (j + J) i)
  let h := fun j x => max 0 ((D (j + J)).scalarCurvature x)
  let d := fun j => 1 + ∫ x in W (j + J), K (j + J) x ∂μ j
  let w := fun j i => 1 + ∫ x in E j i, K (j + J) x ∂μ j
  have hmeas (j : ℕ) (x : M j) (r : ℝ) : MeasurableSet ((g j).ball x r) := by
    rw [← (g j).toMetricSpace_ball]
    exact Metric.isOpen_ball.measurableSet
  have hd (j : ℕ) : 0 < d j := by
    have hnK : 0 ≤ ∫ x in W (j + J), K (j + J) x ∂μ j := integral_nonneg (hKn _)
    dsimp [d]
    linarith
  have hw (j : ℕ) (i : ι) : 0 < w j i := by
    have hnK : 0 ≤ ∫ x in E j i, K (j + J) x ∂μ j := integral_nonneg (hKn _)
    dsimp [w]
    linarith
  have hwd (j : ℕ) (i : ι) : w j i ≤ d j := by
    apply add_le_add_right
    exact setIntegral_mono_set (hKi _) (Filter.Eventually.of_forall (hKn _))
      (Filter.Eventually.of_forall (hDoubleBuffer _ i))
  have houtside (j : ℕ) :
      (∫ x in U j \ ⋃ i, V j i, h j x ∂μ j) ≤ (|A| + |B|) * d j := by
    obtain ⟨hcov, hord, hcrit⟩ := hJ (j + J) (by omega)
    have hb := (D (j + J)).integral_scalarCurvature_posPart_outside_iUnion_ball_le_of_weighted_mixed_annuli
      hn (hcomplete _) (p _) (o _) s C₀ D₀ (q _) (a _) r₀ R C
      (ha _) hr₀ hR hC hm (hW _) (hKi _) (hKn _) hL hD₀
      (hOrdBuffer _) (hCritBuffer _) hcov hord hcrit
    change (∫ x in U j \ ⋃ i, V j i, h j x ∂μ j) ≤
      A + B * ∫ x in W (j + J), K (j + J) x ∂μ j at hb
    have hI : 0 ≤ ∫ x in W (j + J), K (j + J) x ∂μ j := integral_nonneg (hKn _)
    apply hb.trans
    dsimp [d]
    have hBA := mul_le_mul_of_nonneg_right (le_abs_self B) hI
    have hpos := mul_nonneg (abs_nonneg A) hI
    nlinarith [le_abs_self A, abs_nonneg B]
  have hlarge' : ∀ T : ℝ, ∃ j, T < (∫ x in U j, h j x ∂μ j) / d j := by
    intro T
    exact ((hlarge.comp (tendsto_add_atTop_nat J)).eventually (eventually_gt_atTop T)).exists
  obtain ⟨i, φ, hφ, hdiv⟩ :=
    Poincare.CurvatureIntegral.exists_subseq_fixed_member_integral_ratio_tendsto_atTop
      μ U V h (fun j => hmeas _ _ _) (fun j i => hmeas _ _ _)
      (fun _ _ => le_max_left _ _)
      (fun j => (g (j + J)).integrableOn_ball_of_continuous (hcomplete _)
        (continuous_const.max (D (j + J)).continuous_scalarCurvature) _ _)
      (fun j i => (g (j + J)).integrableOn_ball_of_continuous (hcomplete _)
        (continuous_const.max (D (j + J)).continuous_scalarCurvature) _ _)
      d hd w hw hwd (|A| + |B|) houtside hlarge'
  obtain ⟨J', hJ'⟩ := eventually_atTop.mp (hdiv.eventually (eventually_gt_atTop 0))
  let ψ := fun j => φ (j + J') + J
  have hψ : StrictMono ψ := fun x y hxy =>
    Nat.add_lt_add_right (hφ (Nat.add_lt_add_right hxy J')) J
  have hpos (j : ℕ) : 0 < a (ψ j) i := by
    by_contra hnpos
    have haz : a (ψ j) i = 0 := le_antisymm (le_of_not_gt hnpos) (ha _ _)
    have hball : V (φ (j + J')) i = ∅ := by
      dsimp [V]
      change (g (ψ j)).ball (q (ψ j) i) (4 * a (ψ j) i) = ∅
      rw [haz, mul_zero, ← (g (ψ j)).toMetricSpace_ball, Metric.ball_zero]
    have ht := hJ' (j + J') (by omega)
    rw [hball, setIntegral_empty, zero_div] at ht
    exact (lt_irrefl 0) ht
  have hposdiv : Tendsto (fun j =>
      (∫ x in (g (ψ j)).ball (q (ψ j) i) (4 * a (ψ j) i),
        max 0 ((D (ψ j)).scalarCurvature x) ∂(g (ψ j)).volumeMeasure) /
          (1 + ∫ x in (g (ψ j)).ball (q (ψ j) i) (8 * a (ψ j) i),
            K (ψ j) x ∂(g (ψ j)).volumeMeasure)) atTop atTop :=
    hdiv.comp (tendsto_add_atTop_nat J')
  refine ⟨i, ψ, hψ, hpos, hposdiv, ?_⟩
  apply tendsto_atTop.2
  intro T
  filter_upwards [(tendsto_atTop.1 hposdiv) (T + (n : ℝ) ^ 2)] with j hj
  have hsub : (g (ψ j)).ball (q (ψ j) i) (4 * a (ψ j) i) ⊆
      (g (ψ j)).ball (q (ψ j) i) (8 * a (ψ j) i) := by
    rw [← (g (ψ j)).toMetricSpace_ball, ← (g (ψ j)).toMetricSpace_ball]
    exact Metric.ball_subset_ball (by nlinarith [ha (ψ j) i])
  have hb := (D (ψ j)).normalized_integral_scalarCurvature_posPart_le_add_of_subset
    (hmeas _ _ _) hsub (hKn _) (fun x _ => hsec _ x)
    ((g (ψ j)).integrableOn_ball_of_continuous (hcomplete _)
      (D (ψ j)).continuous_scalarCurvature _ _)
    ((hKi _).mono_set (hDoubleBuffer _ i))
  linarith

end PoincareConjecture
