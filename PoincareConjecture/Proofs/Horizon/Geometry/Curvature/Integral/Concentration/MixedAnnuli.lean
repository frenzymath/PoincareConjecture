import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.AnnularConcentration
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.PositiveRadii

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

theorem integral_scalarCurvature_posPart_outside_iUnion_ball_le_of_mixed_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) (hcomplete : MetricComplete g) (p : M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (o : κ → M) (s C₀ : κ → ℝ)
    (q : ι → M) (a r₀ R C : ι → ℝ) {m : ℕ}
    (ha : ∀ i, 0 ≤ a i) (hr₀ : ∀ i, 0 < r₀ i)
    (hR : ∀ i, R i < 19 * r₀ i / 16) (hC : ∀ i, 0 ≤ C i) (hm : 1 ≤ m)
    (hcover : g.ball p 1 ⊆
      (⋃ i, {x : M | (g.edist (o i) x).toReal ∈ Icc (113 * s i / 96) (19 * s i / 16)}) ∪
        ⋃ i, g.ball (q i) (R i))
    (hordinary : ∀ i,
      (∫ x in {x : M | (g.edist (o i) x).toReal ∈ Icc (113 * s i / 96) (19 * s i / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C₀ i)
    (hbound : ∀ i, ∀ r : ℝ, 0 < r → 2 * a i ≤ r → r ≤ r₀ i →
      (∫ x in {x : M | (g.edist (q i) x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C i * r ^ m) :
    (∫ x in g.ball p 1 \ ⋃ i, g.ball (q i) (4 * a i),
      max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
        (∑ i, C₀ i) + ∑ i, C i * r₀ i ^ m / (1 - (227 / 228 : ℝ) ^ m) := by
  classical
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let := g.toMetricSpace
  let E := g.ball p 1 \ ⋃ i, g.ball (q i) (4 * a i)
  let A := fun i => {x : M | (g.edist (o i) x).toReal ∈
    Icc (113 * s i / 96) (19 * s i / 16)}
  let B := fun i => g.ball (q i) (R i) \ g.ball (q i) (4 * a i)
  let T : κ ⊕ ι → Set M := Sum.elim A B
  let h : M → ℝ := fun x => max 0 (D.scalarCurvature x)
  have hmeas (x : M) (r : ℝ) : MeasurableSet (g.ball x r) := by
    rw [← g.toMetricSpace_ball]
    exact Metric.isOpen_ball.measurableSet
  have hcont : Continuous h := continuous_const.max D.continuous_scalarCurvature
  have hEm : MeasurableSet E := (hmeas p 1).diff
    (MeasurableSet.iUnion (fun i => hmeas (q i) (4 * a i)))
  have hAm (i : κ) : MeasurableSet (A i) := by
    change MeasurableSet {x : M | dist (o i) x ∈ Icc _ _}
    exact (isClosed_Icc.preimage (continuous_const.dist continuous_id)).measurableSet
  have hBm (i : ι) : MeasurableSet (B i) :=
    (hmeas (q i) (R i)).diff (hmeas (q i) (4 * a i))
  have hEi : IntegrableOn h E g.volumeMeasure :=
    (g.integrableOn_ball_of_continuous hcomplete hcont p 1).mono_set sdiff_subset
  have hAi (i : κ) : IntegrableOn h (A i) g.volumeMeasure := by
    apply (g.integrableOn_ball_of_continuous hcomplete hcont (o i) (19 * s i / 16 + 1)).mono_set
    intro x hx
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm]
    change dist (o i) x ∈ Icc _ _ at hx
    linarith only [hx.2]
  have hBi (i : ι) : IntegrableOn h (B i) g.volumeMeasure :=
    (g.integrableOn_ball_of_continuous hcomplete hcont (q i) (R i)).mono_set sdiff_subset
  have hTm (i : κ ⊕ ι) : MeasurableSet (T i) := by
    cases i with
    | inl i => exact hAm i
    | inr i => exact hBm i
  have hTi (i : κ ⊕ ι) : IntegrableOn h (T i) g.volumeMeasure := by
    cases i with
    | inl i => exact hAi i
    | inr i => exact hBi i
  have hET : E ⊆ ⋃ i ∈ (Finset.univ : Finset (κ ⊕ ι)), T i := by
    intro x hx
    rcases hcover hx.1 with ho | hq
    · obtain ⟨i, hi⟩ := mem_iUnion.mp ho
      exact mem_iUnion₂.mpr ⟨.inl i, Finset.mem_univ _, hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hq
      refine mem_iUnion₂.mpr ⟨.inr i, Finset.mem_univ _, hi, ?_⟩
      exact fun hb => hx.2 (mem_iUnion.mpr ⟨i, hb⟩)
  apply (Poincare.CurvatureIntegral.integral_le_sum_of_finset_cover hEm
    Finset.univ T (fun i _ => hTm i) (fun _ => le_max_left _ _) hEi
    (fun i _ => hTi i) hET).trans
  rw [Fintype.sum_sum_type]
  exact add_le_add
    (Finset.sum_le_sum fun i _ => hordinary i)
    (Finset.sum_le_sum fun i _ =>
      D.integral_scalarCurvature_posPart_outside_ball_le_of_nonneg_scale_annuli
        hn hcomplete (q i) (ha i) (hr₀ i) (hR i) (hC i) hm (hbound i))

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture

theorem exists_subseq_critical_ball_scalar_integral_tendsto_atTop_of_mixed_annuli
    {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (p : ∀ j, M j) (o : ∀ j, κ → M j) (s C₀ : κ → ℝ)
    (q : ∀ j, ι → M j) (a : ℕ → ι → ℝ) (r₀ R C : ι → ℝ)
    (hn : 1 ≤ n) {m : ℕ} (hm : 1 ≤ m)
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    {A : ℝ} (hA : 0 < A) (ha : ∀ j i, 0 ≤ a j i) (haA : ∀ j i, a j i ≤ A)
    (hr₀ : ∀ i, 0 < r₀ i) (hR : ∀ i, R i < 19 * r₀ i / 16)
    (hC : ∀ i, 0 ≤ C i)
    (hevent : ∀ᶠ j in atTop,
      ((g j).ball (p j) 1 ⊆
        (⋃ i, {x : M j | ((g j).edist (o j i) x).toReal ∈
          Icc (113 * s i / 96) (19 * s i / 16)}) ∪
            ⋃ i, (g j).ball (q j i) (R i)) ∧
      (∀ i, (∫ x in {x : M j | ((g j).edist (o j i) x).toReal ∈
          Icc (113 * s i / 96) (19 * s i / 16)},
        max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C₀ i) ∧
      (∀ i, ∀ r : ℝ, 0 < r → 2 * a j i ≤ r → r ≤ r₀ i →
        (∫ x in {x : M j | ((g j).edist (q j i) x).toReal ∈
            Icc (113 * r / 96) (19 * r / 16)},
          max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C i * r ^ m))
    (hlarge : Tendsto (fun j => ∫ x in (g j).ball (p j) 1,
      (D j).scalarCurvature x ∂(g j).volumeMeasure) atTop atTop) :
    ∃ i : ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ j, 0 < a (φ j) i) ∧
      Tendsto (fun j => ∫ x in (g (φ j)).ball (q (φ j) i) (4 * a (φ j) i),
        (D (φ j)).scalarCurvature x ∂(g (φ j)).volumeMeasure) atTop atTop := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hevent
  let B := (∑ i, C₀ i) + ∑ i, C i * r₀ i ^ m / (1 - (227 / 228 : ℝ) ^ m)
  have houtside (j : ℕ) :
      (∫ x in (g (j + J)).ball (p (j + J)) 1 \
          ⋃ i, (g (j + J)).ball (q (j + J) i) (4 * a (j + J) i),
        max 0 ((D (j + J)).scalarCurvature x) ∂(g (j + J)).volumeMeasure) ≤ B := by
    obtain ⟨hcov, hord, hcrit⟩ := hJ (j + J) (by omega)
    exact (D (j + J)).integral_scalarCurvature_posPart_outside_iUnion_ball_le_of_mixed_annuli
      hn (hcomplete (j + J)) (p (j + J)) (o (j + J)) s C₀
      (q (j + J)) (a (j + J)) r₀ R C (ha (j + J)) hr₀ hR hC hm hcov hord hcrit
  have hlarge' : ∀ B : ℝ, ∃ j, B < ∫ x in (g (j + J)).ball (p (j + J)) 1,
      (D (j + J)).scalarCurvature x ∂(g (j + J)).volumeMeasure := by
    intro B
    exact ((hlarge.comp (tendsto_add_atTop_nat J)).eventually (eventually_gt_atTop B)).exists
  obtain ⟨i, φ, hφ, hpos, hdiv⟩ :=
    exists_subseq_prescribed_center_scalar_integral_tendsto_atTop_with_positive_radii
      (fun j => g (j + J)) (fun j => D (j + J)) (fun j => p (j + J))
      (fun j => q (j + J)) (fun j i => 4 * a (j + J) i)
      hn (show 0 < 4 * A by positivity)
      (fun j i => mul_le_mul_of_nonneg_left (haA (j + J) i) (by norm_num))
      (fun j => hcomplete (j + J)) (fun j => hsec (j + J)) B houtside hlarge'
  refine ⟨i, fun j => φ j + J,
    fun x y hxy => Nat.add_lt_add_right (hφ hxy) J, ?_, hdiv⟩
  intro j
  linarith only [hpos j]

end PoincareConjecture
