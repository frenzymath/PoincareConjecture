import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.AnnulusOverlap
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.ScalarAnnuli










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators
namespace PoincareConjecture.LeviCivitaData

theorem integral_scalarCurvature_posPart_outside_ball_le_of_weighted_scale_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (p : M)
    {W : Set M} {K : M → ℝ} (hW : MeasurableSet W)
    (hKint : IntegrableOn K W g.volumeMeasure) (hKn : ∀ x, 0 ≤ K x)
    {a r₀ R C : ℝ} {m : ℕ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hR : R < 19 * r₀ / 16) (hC : 0 ≤ C) (hm : 1 ≤ m)
    {L : ℕ} (hL : 3 * (227 / 228 : ℝ) ^ L < 1 / 2)
    (hbuffer : {x : M | (g.edist p x).toReal ≤ 3 * r₀} ⊆ W)
    (hbound : ∀ r : ℝ, 2 * a ≤ r → r ≤ r₀ →
      (∫ x in {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C * (r ^ m +
          ∫ x in {x : M | (g.edist p x).toReal ∈ Icc (r / 2) (3 * r)}, K x ∂g.volumeMeasure)) :
    (∫ x in g.ball p R \ g.ball p (4 * a),
      max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
        C * r₀ ^ m / (1 - (227 / 228 : ℝ) ^ m) +
          C * (L : ℝ) * ∫ x in W, K x ∂g.volumeMeasure := by
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  let E := Metric.closedBall p R \ Metric.ball p (4 * a)
  let h : M → ℝ := fun x => max 0 (D.scalarCurvature x)
  have hK : IsCompact E := (isCompact_closedBall p R).diff Metric.isOpen_ball
  have hcont : Continuous h := continuous_const.max D.continuous_scalarCurvature
  have hKi : IntegrableOn h E g.volumeMeasure := hcont.continuousOn.integrableOn_compact hK
  have hsub : E ⊆ {x | (19 / 16 : ℝ) * (2 * a) < dist p x ∧
      dist p x < (19 / 16 : ℝ) * r₀} := by
    intro x hx
    have hlo : 4 * a ≤ dist p x := by
      simpa only [Metric.mem_ball, not_lt, dist_comm] using hx.2
    have hhi : dist p x ≤ R := by
      simpa only [Metric.mem_closedBall, dist_comm] using hx.1
    constructor <;> linarith
  have hri (j : ℕ) : r₀ * (227 / 228 : ℝ) ^ j ≤ r₀ := by
    exact mul_le_of_le_one_right hr₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hAnnulusI (r : ℝ) :
      IntegrableOn h {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)}
        g.volumeMeasure := by
    have hi := g.integrableOn_ball_of_continuous hcomplete hcont p (19 * r / 16 + 1)
    apply hi.mono_set
    intro x hx
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm]
    change dist p x ∈ Icc (113 * r / 96) (19 * r / 16) at hx
    linarith only [hx.2]
  have hOpenSub (r : ℝ) :
      {x : M | (113 / 96 : ℝ) * r < dist p x ∧ dist p x < (19 / 16 : ℝ) * r} ⊆
        {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} := by
    intro x hx
    change dist p x ∈ Icc (113 * r / 96) (19 * r / 16)
    constructor <;> linarith only [hx.1, hx.2]
  have herr (j : ℕ) :
      {x : M | (1 / 2 : ℝ) * (r₀ * (227 / 228 : ℝ) ^ j) ≤ dist p x ∧
        dist p x ≤ 3 * (r₀ * (227 / 228 : ℝ) ^ j)} ⊆ W := by
    intro x hx
    apply hbuffer
    change dist p x ≤ 3 * r₀
    exact hx.2.trans (mul_le_mul_of_nonneg_left (hri j) (by norm_num))
  have hset (r : ℝ) :
      {x : M | (1 / 2 : ℝ) * r ≤ dist p x ∧ dist p x ≤ 3 * r} =
        {x : M | (g.edist p x).toReal ∈ Icc (r / 2) (3 * r)} := by
    ext x
    change ((1 / 2 : ℝ) * r ≤ dist p x ∧ dist p x ≤ 3 * r) ↔
      (r / 2 ≤ dist p x ∧ dist p x ≤ 3 * r)
    rw [show (1 / 2 : ℝ) * r = r / 2 by ring]
  have hKbound := Poincare.CurvatureIntegral.integral_le_of_weighted_geometric_annulus_bounds_above_scale
    hK p hW hKint hKn (A := 113 / 96) (B := 19 / 16)
    (A' := 1 / 2) (B' := 3) (by norm_num) (by norm_num) (by norm_num) hr₀
    (q := 227 / 228) (by norm_num) (by norm_num) (by norm_num)
    hL hC hC hm (s := 2 * a) (by positivity)
    (h := h) (fun x => le_max_left _ _) hKi hsub
    (fun j => (hAnnulusI _).mono_set (hOpenSub _)) herr
    (fun j hj => (setIntegral_mono_set (hAnnulusI _)
      (Filter.Eventually.of_forall (fun _ => le_max_left _ _))
      (Filter.Eventually.of_forall (hOpenSub _))).trans (by
        rw [hset, ← mul_add]
        exact hbound _ hj (hri j)))
  apply (setIntegral_mono_set hKi
    (Filter.Eventually.of_forall (fun _ => le_max_left _ _)) ?_).trans hKbound
  apply Filter.Eventually.of_forall
  intro x hx
  rw [← g.toMetricSpace_ball, ← g.toMetricSpace_ball] at hx
  exact ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩



theorem integral_scalarCurvature_posPart_ball_le_of_all_weighted_scale_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) (hcomplete : MetricComplete g) (p : M)
    {W : Set M} {K : M → ℝ} (hW : MeasurableSet W)
    (hKint : IntegrableOn K W g.volumeMeasure) (hKn : ∀ x, 0 ≤ K x)
    {r₀ R C : ℝ} {m : ℕ} (hr₀ : 0 < r₀)
    (hR : R < 19 * r₀ / 16) (hC : 0 ≤ C) (hm : 1 ≤ m)
    {L : ℕ} (hL : 3 * (227 / 228 : ℝ) ^ L < 1 / 2)
    (hbuffer : {x : M | (g.edist p x).toReal ≤ 3 * r₀} ⊆ W)
    (hbound : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫ x in {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C * (r ^ m +
          ∫ x in {x : M | (g.edist p x).toReal ∈ Icc (r / 2) (3 * r)}, K x ∂g.volumeMeasure)) :
    (∫ x in g.ball p R, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      C * r₀ ^ m / (1 - (227 / 228 : ℝ) ^ m) +
          C * (L : ℝ) * ∫ x in W, K x ∂g.volumeMeasure := by
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let := g.toMetricSpace
  let : NullSingletonClass g.volumeMeasure := g.volumeMeasure_nullSingletonClass hn
  apply Poincare.CurvatureIntegral.integral_le_of_compl_ball_bounds
    (by rw [← g.toMetricSpace_ball]; exact Metric.isOpen_ball.measurableSet)
    (g.integrableOn_ball_of_continuous hcomplete
      (continuous_const.max D.continuous_scalarCurvature) p R) p
  intro a ha
  have hb := D.integral_scalarCurvature_posPart_outside_ball_le_of_weighted_scale_annuli
    hcomplete p hW hKint hKn (a := a / 4) (by positivity) hr₀ hR hC hm hL hbuffer
    (fun r hr hr' => hbound r (by linarith) hr')
  rw [show 4 * (a / 4) = a by ring, ← g.toMetricSpace_ball p a] at hb
  exact hb



theorem integral_scalarCurvature_posPart_outside_ball_le_of_nonneg_weighted_scale_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) (hcomplete : MetricComplete g) (p : M)
    {W : Set M} {K : M → ℝ} (hW : MeasurableSet W)
    (hKint : IntegrableOn K W g.volumeMeasure) (hKn : ∀ x, 0 ≤ K x)
    {a r₀ R C : ℝ} {m : ℕ} (ha : 0 ≤ a) (hr₀ : 0 < r₀)
    (hR : R < 19 * r₀ / 16) (hC : 0 ≤ C) (hm : 1 ≤ m)
    {L : ℕ} (hL : 3 * (227 / 228 : ℝ) ^ L < 1 / 2)
    (hbuffer : {x : M | (g.edist p x).toReal ≤ 3 * r₀} ⊆ W)
    (hbound : ∀ r : ℝ, 0 < r → 2 * a ≤ r → r ≤ r₀ →
      (∫ x in {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C * (r ^ m +
          ∫ x in {x : M | (g.edist p x).toReal ∈ Icc (r / 2) (3 * r)}, K x ∂g.volumeMeasure)) :
    (∫ x in g.ball p R \ g.ball p (4 * a),
      max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
        C * r₀ ^ m / (1 - (227 / 228 : ℝ) ^ m) +
          C * (L : ℝ) * ∫ x in W, K x ∂g.volumeMeasure := by
  rcases ha.eq_or_lt with rfl | ha
  · let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
    let := g.toMetricSpace
    have hb := D.integral_scalarCurvature_posPart_ball_le_of_all_weighted_scale_annuli
      hn hcomplete p hW hKint hKn hr₀ hR hC hm hL hbuffer (fun r hr hr' => hbound r hr (by simpa using hr.le) hr')
    simpa only [mul_zero, ← g.toMetricSpace_ball p 0, Metric.ball_zero, sdiff_empty] using hb
  · exact D.integral_scalarCurvature_posPart_outside_ball_le_of_weighted_scale_annuli
      hcomplete p hW hKint hKn ha hr₀ hR hC hm hL hbuffer (fun r hr hr' => hbound r (by linarith) hr hr')


theorem integral_scalarCurvature_posPart_outside_iUnion_ball_le_of_weighted_mixed_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) (hcomplete : MetricComplete g) (p : M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (o : κ → M) (s C₀ D₀ : κ → ℝ)
    (q : ι → M) (a r₀ R C : ι → ℝ) {m : ℕ}
    (ha : ∀ i, 0 ≤ a i) (hr₀ : ∀ i, 0 < r₀ i)
    (hR : ∀ i, R i < 19 * r₀ i / 16) (hC : ∀ i, 0 ≤ C i) (hm : 1 ≤ m)
    {W : Set M} {K : M → ℝ} (hW : MeasurableSet W)
    (hKi : IntegrableOn K W g.volumeMeasure) (hKn : ∀ x, 0 ≤ K x)
    {L : ℕ} (hL : 3 * (227 / 228 : ℝ) ^ L < 1 / 2)
    (hD₀ : ∀ i, 0 ≤ D₀ i)
    (hOrdBuffer : ∀ i,
      {x : M | (g.edist (o i) x).toReal ∈ Icc (s i / 2) (3 * s i)} ⊆ W)
    (hCritBuffer : ∀ i, {x : M | (g.edist (q i) x).toReal ≤ 3 * r₀ i} ⊆ W)
    (hcover : g.ball p 1 ⊆
      (⋃ i, {x : M | (g.edist (o i) x).toReal ∈ Icc (113 * s i / 96) (19 * s i / 16)}) ∪
        ⋃ i, g.ball (q i) (R i))
    (hordinary : ∀ i,
      (∫ x in {x : M | (g.edist (o i) x).toReal ∈ Icc (113 * s i / 96) (19 * s i / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C₀ i + D₀ i *
        ∫ x in {x : M | (g.edist (o i) x).toReal ∈ Icc (s i / 2) (3 * s i)}, K x ∂g.volumeMeasure)
    (hbound : ∀ i, ∀ r : ℝ, 0 < r → 2 * a i ≤ r → r ≤ r₀ i →
      (∫ x in {x : M | (g.edist (q i) x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C i * (r ^ m +
        ∫ x in {x : M | (g.edist (q i) x).toReal ∈ Icc (r / 2) (3 * r)}, K x ∂g.volumeMeasure)) :
    (∫ x in g.ball p 1 \ ⋃ i, g.ball (q i) (4 * a i),
      max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
        (∑ i, C₀ i) + (∑ i, C i * r₀ i ^ m / (1 - (227 / 228 : ℝ) ^ m)) +
          ((∑ i, D₀ i) + (L : ℝ) * ∑ i, C i) * ∫ x in W, K x ∂g.volumeMeasure := by
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
  have hord (i : κ) : (∫ x in A i, h x ∂g.volumeMeasure) ≤
      C₀ i + D₀ i * ∫ x in W, K x ∂g.volumeMeasure := by
    apply (hordinary i).trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (hD₀ i)
    exact setIntegral_mono_set hKi (Filter.Eventually.of_forall hKn)
      (Filter.Eventually.of_forall (hOrdBuffer i))
  have hc (i : ι) := D.integral_scalarCurvature_posPart_outside_ball_le_of_nonneg_weighted_scale_annuli
    hn hcomplete (q i) hW hKi hKn (ha i) (hr₀ i) (hR i) (hC i) hm hL
    (hCritBuffer i) (hbound i)
  calc
    _ ≤ (∑ i, (C₀ i + D₀ i * ∫ x in W, K x ∂g.volumeMeasure)) +
        ∑ i, (C i * r₀ i ^ m / (1 - (227 / 228 : ℝ) ^ m) +
          C i * (L : ℝ) * ∫ x in W, K x ∂g.volumeMeasure) :=
      add_le_add (Finset.sum_le_sum fun i _ => hord i)
        (Finset.sum_le_sum fun i _ => hc i)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]; ring

end PoincareConjecture.LeviCivitaData
