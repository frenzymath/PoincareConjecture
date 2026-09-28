import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberCompact

open Set Filter MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.RiemannianMetric.integral_openFiber_pos_scalar_outside_ambient_ball_le
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M) (hc : PoincareConjecture.MetricComplete g)
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (p : openFiber f U c)
    {a r₀ R C : ℝ} {d L : ℕ}
    (ha : 0 < a) (hr₀ : 0 < r₀) (hR : 0 ≤ R) (hR' : R < 19*r₀/16)
    (hC : 0 ≤ C) (hd : 1 ≤ d) (hL : 3 * (227 / 228 : ℝ)^L < 1/2)
    (hball : ∀ y, g.edist (openFiberIncl f U c p) y ≤ ENNReal.ofReal (3*r₀) → y ∈ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    ∀ (D : PoincareConjecture.LeviCivitaData gL) (W : Set (openFiber f U c))
      (K : openFiber f U c → ℝ),
    MeasurableSet W → IntegrableOn K W gL.volumeMeasure → (∀ x, 0 ≤ K x) →
    ({x | (g.edist (incl p) (incl x)).toReal ≤ 3*r₀} ⊆ W) →
    (∀ r : ℝ, 2*a ≤ r → r ≤ r₀ →
      (∫ x in {x | (g.edist (incl p) (incl x)).toReal ∈ Icc (113*r/96) (19*r/16)},
        max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤
        C * (r^d + ∫ x in {x | (g.edist (incl p) (incl x)).toReal ∈ Icc (r/2) (3*r)},
          K x ∂gL.volumeMeasure)) →
    (∫ x in incl ⁻¹' (g.ball (incl p) R) \ incl ⁻¹' (g.ball (incl p) (4*a)),
      max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤
      C*r₀^d/(1-(227/228:ℝ)^d) + C*(L:ℝ)*∫ x in W, K x ∂gL.volumeMeasure := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  dsimp only
  intro D W K hW hKint hKn hbuffer hbound
  let : ConnectedSpace M := { toNonempty := ⟨incl p⟩ }
  let := g.toMetricSpace
  let : MetricSpace (openFiber f U c) :=
    (isEmbedding_openFiberIncl f U c).comapMetricSpace incl
  have hdist (x y : openFiber f U c) :
      dist x y = (g.edist (incl x) (incl y)).toReal := rfl
  have hcpt (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 3*r₀) :
      IsCompact (Metric.closedBall p s : Set (openFiber f U c)) := by
    have hh := g.isCompact_openFiber_preimage_closedBall hc hf.continuous U c
      (incl p) s (fun y hy => hball y (hy.trans (ENNReal.ofReal_le_ofReal hs')))
    convert hh using 1
    ext z
    change dist z p ≤ s ↔ g.edist (incl p) (incl z) ≤ ENNReal.ofReal s
    rw [dist_comm, hdist]
    constructor
    · intro hz
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top (incl p) (incl z))]
      exact ENNReal.ofReal_le_ofReal hz
    · exact ENNReal.toReal_le_of_le_ofReal hs
  let E := Metric.closedBall p R \ Metric.ball p (4*a)
  let H := fun x => max 0 (D.scalarCurvature x)
  have hE : IsCompact E := (hcpt R hR (by linarith)).diff Metric.isOpen_ball
  have hcont : Continuous H := continuous_const.max D.continuous_scalarCurvature
  have hEi : IntegrableOn H E gL.volumeMeasure := hcont.continuousOn.integrableOn_compact hE
  have hsub : E ⊆ {x | (19/16:ℝ)*(2*a)<dist p x ∧ dist p x<(19/16:ℝ)*r₀} := by
    intro x hx
    have hlo : 4*a ≤ dist p x := by
      simpa only [Metric.mem_ball, not_lt, dist_comm] using hx.2
    have hhi : dist p x ≤ R := by
      simpa only [Metric.mem_closedBall, dist_comm] using hx.1
    constructor <;> linarith
  have hri (j : ℕ) : r₀*(227/228:ℝ)^j ≤ r₀ :=
    mul_le_of_le_one_right hr₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hi (j : ℕ) :
      IntegrableOn H {x | (g.edist (incl p) (incl x)).toReal ∈
        Icc (113*(r₀*(227/228:ℝ)^j)/96) (19*(r₀*(227/228:ℝ)^j)/16)} gL.volumeMeasure := by
    apply (hcont.continuousOn.integrableOn_compact (hcpt (2*r₀) (by positivity) (by linarith))).mono_set
    intro x hx
    rw [Metric.mem_closedBall, dist_comm, hdist]
    exact hx.2.trans (by nlinarith only [hri j, hr₀])
  have hopen (r : ℝ) :
      {x : openFiber f U c | (113/96:ℝ)*r<dist p x ∧ dist p x<(19/16:ℝ)*r} ⊆
        {x | (g.edist (incl p) (incl x)).toReal ∈ Icc (113*r/96) (19*r/16)} := by
    intro x hx
    change dist p x ∈ Icc (113*r/96) (19*r/16)
    constructor <;> linarith only [hx.1,hx.2]
  have herr (j : ℕ) :
      {x : openFiber f U c | (1/2:ℝ)*(r₀*(227/228:ℝ)^j) ≤ dist p x ∧
        dist p x ≤ 3*(r₀*(227/228:ℝ)^j)} ⊆ W := by
    intro x hx
    apply hbuffer
    change dist p x ≤ 3*r₀
    exact hx.2.trans (mul_le_mul_of_nonneg_left (hri j) (by norm_num))
  have hset (r : ℝ) :
      {x : openFiber f U c | (1/2:ℝ)*r ≤ dist p x ∧ dist p x ≤ 3*r} =
        {x | (g.edist (incl p) (incl x)).toReal ∈ Icc (r/2) (3*r)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    rw [hdist]
    rw [show (1/2:ℝ)*r=r/2 by ring]
  have hb := Poincare.CurvatureIntegral.integral_le_of_weighted_geometric_annulus_bounds_above_scale
    hE p hW hKint hKn (A := 113/96) (B := 19/16) (A' := 1/2) (B' := 3)
    (by norm_num) (by norm_num) (by norm_num) hr₀
    (q := 227/228) (by norm_num) (by norm_num) (by norm_num)
    hL hC hC hd (s := 2*a) (by positivity) (h := H)
    (fun x => le_max_left _ _) hEi hsub (fun j => (hi j).mono_set (hopen _)) herr
    (fun j hj => (setIntegral_mono_set (hi j)
      (Filter.Eventually.of_forall (fun _ => le_max_left _ _))
      (Filter.Eventually.of_forall (hopen _))).trans (by
        rw [hset, ← mul_add]
        exact hbound _ hj (hri j)))
  apply (setIntegral_mono_set hEi
    (Filter.Eventually.of_forall (fun _ => le_max_left _ _)) ?_).trans hb
  apply Filter.Eventually.of_forall
  intro x hx
  have hballEq (s : ℝ) : incl ⁻¹' (g.ball (incl p) s) = Metric.ball p s := by
    rw [← g.toMetricSpace_ball]
    rfl
  rw [hballEq, hballEq] at hx
  exact ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩

theorem PoincareConjecture.RiemannianMetric.integral_openFiber_pos_scalar_ambient_ball_le
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M) (hc : PoincareConjecture.MetricComplete g)
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (p : openFiber f U c)
    {r₀ R C : ℝ} {d L : ℕ}
    (hm : 0 < m) (hr₀ : 0 < r₀) (hR : 0 ≤ R) (hR' : R < 19*r₀/16)
    (hC : 0 ≤ C) (hd : 1 ≤ d) (hL : 3 * (227 / 228 : ℝ)^L < 1/2)
    (hball : ∀ y, g.edist (openFiberIncl f U c p) y ≤ ENNReal.ofReal (3*r₀) → y ∈ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    ∀ (D : PoincareConjecture.LeviCivitaData gL) (W : Set (openFiber f U c))
      (K : openFiber f U c → ℝ),
    MeasurableSet W → IntegrableOn K W gL.volumeMeasure → (∀ x, 0 ≤ K x) →
    ({x | (g.edist (incl p) (incl x)).toReal ≤ 3*r₀} ⊆ W) →
    (∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫ x in {x | (g.edist (incl p) (incl x)).toReal ∈ Icc (113*r/96) (19*r/16)},
        max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤
        C * (r^d + ∫ x in {x | (g.edist (incl p) (incl x)).toReal ∈ Icc (r/2) (3*r)},
          K x ∂gL.volumeMeasure)) →
    (∫ x in incl ⁻¹' (g.ball (incl p) R),
      max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤
      C*r₀^d/(1-(227/228:ℝ)^d) + C*(L:ℝ)*∫ x in W, K x ∂gL.volumeMeasure := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  dsimp only
  intro D W K hW hKint hKn hbuffer hbound
  let : ConnectedSpace M := { toNonempty := ⟨incl p⟩ }
  let := g.toMetricSpace
  let : MetricSpace (openFiber f U c) :=
    (isEmbedding_openFiberIncl f U c).comapMetricSpace incl
  have hdist (x y : openFiber f U c) :
      dist x y = (g.edist (incl x) (incl y)).toReal := rfl
  have hcpt (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 3*r₀) :
      IsCompact (Metric.closedBall p s : Set (openFiber f U c)) := by
    have hh := g.isCompact_openFiber_preimage_closedBall hc hf.continuous U c
      (incl p) s (fun y hy => hball y (hy.trans (ENNReal.ofReal_le_ofReal hs')))
    convert hh using 1
    ext z
    change dist z p ≤ s ↔ g.edist (incl p) (incl z) ≤ ENNReal.ofReal s
    rw [dist_comm, hdist]
    constructor
    · intro hz
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top (incl p) (incl z))]
      exact ENNReal.ofReal_le_ofReal hz
    · exact ENNReal.toReal_le_of_le_ofReal hs
  let : NullSingletonClass gL.volumeMeasure := gL.volumeMeasure_nullSingletonClass hm
  have hballEq (s : ℝ) : incl ⁻¹' (g.ball (incl p) s) = Metric.ball p s := by
    rw [← g.toMetricSpace_ball]
    rfl
  have hi : IntegrableOn (fun x => max 0 (D.scalarCurvature x))
      (incl ⁻¹' (g.ball (incl p) R)) gL.volumeMeasure := by
    rw [hballEq]
    exact ((continuous_const.max D.continuous_scalarCurvature).continuousOn.integrableOn_compact
      (hcpt R hR (by linarith))).mono_set Metric.ball_subset_closedBall
  apply Poincare.CurvatureIntegral.integral_le_of_compl_ball_bounds
    (by rw [hballEq]; exact Metric.isOpen_ball.measurableSet) hi p
  intro a ha
  have hb := g.integral_openFiber_pos_scalar_outside_ambient_ball_le hc hf U hreg c p
    (a := a/4) (by positivity) hr₀ hR hR' hC hd hL hball D W K hW hKint hKn hbuffer
    (fun r hr hr' => hbound r (by linarith) hr')
  rw [show 4*(a/4)=a by ring, hballEq a] at hb
  exact hb

theorem PoincareConjecture.RiemannianMetric.integral_openFiber_pos_scalar_outside_ambient_ball_le_of_nonneg
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M) (hc : PoincareConjecture.MetricComplete g)
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (p : openFiber f U c)
    {a r₀ R C : ℝ} {d L : ℕ}
    (hm : 0 < m) (ha : 0 ≤ a) (hr₀ : 0 < r₀) (hR : 0 ≤ R) (hR' : R < 19*r₀/16)
    (hC : 0 ≤ C) (hd : 1 ≤ d) (hL : 3 * (227 / 228 : ℝ)^L < 1/2)
    (hball : ∀ y, g.edist (openFiberIncl f U c p) y ≤ ENNReal.ofReal (3*r₀) → y ∈ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    ∀ (D : PoincareConjecture.LeviCivitaData gL) (W : Set (openFiber f U c))
      (K : openFiber f U c → ℝ),
    MeasurableSet W → IntegrableOn K W gL.volumeMeasure → (∀ x, 0 ≤ K x) →
    ({x | (g.edist (incl p) (incl x)).toReal ≤ 3*r₀} ⊆ W) →
    (∀ r : ℝ, 0 < r → 2*a ≤ r → r ≤ r₀ →
      (∫ x in {x | (g.edist (incl p) (incl x)).toReal ∈ Icc (113*r/96) (19*r/16)},
        max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤
        C * (r^d + ∫ x in {x | (g.edist (incl p) (incl x)).toReal ∈ Icc (r/2) (3*r)},
          K x ∂gL.volumeMeasure)) →
    (∫ x in incl ⁻¹' (g.ball (incl p) R) \ incl ⁻¹' (g.ball (incl p) (4*a)),
      max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤
      C*r₀^d/(1-(227/228:ℝ)^d) + C*(L:ℝ)*∫ x in W, K x ∂gL.volumeMeasure := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  dsimp only
  intro D W K hW hKint hKn hbuffer hbound
  rcases ha.eq_or_lt with rfl | ha
  · let : ConnectedSpace M := { toNonempty := ⟨incl p⟩ }
    let := g.toMetricSpace
    have hb := g.integral_openFiber_pos_scalar_ambient_ball_le hc hf U hreg c p
      hm hr₀ hR hR' hC hd hL hball D W K hW hKint hKn hbuffer
      (fun r hr hr' => hbound r hr (by simpa using hr.le) hr')
    have he : g.ball (openFiberIncl f U c p) 0 = ∅ := by
      rw [← g.toMetricSpace_ball]
      exact Metric.ball_zero
    simpa only [mul_zero, he, preimage_empty, sdiff_empty] using hb
  · exact g.integral_openFiber_pos_scalar_outside_ambient_ball_le hc hf U hreg c p
      ha hr₀ hR hR' hC hd hL hball D W K hW hKint hKn hbuffer
      (fun r hr hr' => hbound r (by linarith) hr hr')

theorem PoincareConjecture.RiemannianMetric.integral_openFiber_pos_scalar_outside_iUnion_ambient_ball_le_of_weighted_mixed_annuli
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M) (hc : PoincareConjecture.MetricComplete g)
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (p : openFiber f U c) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    ∀ (D : PoincareConjecture.LeviCivitaData gL)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (o : κ → openFiber f U c) (s C₀ D₀ : κ → ℝ)
    (q : ι → openFiber f U c) (a r₀ R C : ι → ℝ) {d : ℕ}
    (hm : 0 < m) (hs : ∀ i, 0 ≤ s i) (hRn : ∀ i, 0 ≤ R i)
    (hMainBall : ∀ y, g.edist (incl p) y ≤ ENNReal.ofReal 1 → y ∈ U)
    (hOrdBall : ∀ i y, g.edist (incl (o i)) y ≤ ENNReal.ofReal (3*s i) → y ∈ U)
    (hCritBall : ∀ i y, g.edist (incl (q i)) y ≤ ENNReal.ofReal (3*r₀ i) → y ∈ U)
    (ha : ∀ i, 0 ≤ a i) (hr₀ : ∀ i, 0 < r₀ i)
    (hR : ∀ i, R i < 19 * r₀ i / 16) (hC : ∀ i, 0 ≤ C i) (hd : 1 ≤ d)
    {W : Set (openFiber f U c)} {K : (openFiber f U c) → ℝ} (hW : MeasurableSet W)
    (hKi : IntegrableOn K W gL.volumeMeasure) (hKn : ∀ x, 0 ≤ K x)
    {L : ℕ} (hL : 3 * (227 / 228 : ℝ) ^ L < 1 / 2)
    (hD₀ : ∀ i, 0 ≤ D₀ i)
    (hOrdBuffer : ∀ i,
      {x : openFiber f U c | (g.edist (incl (o i)) (incl x)).toReal ∈ Icc (s i / 2) (3 * s i)} ⊆ W)
    (hCritBuffer : ∀ i, {x : openFiber f U c | (g.edist (incl (q i)) (incl x)).toReal ≤ 3 * r₀ i} ⊆ W)
    (hcover : (incl ⁻¹' g.ball (incl p) 1) ⊆
      (⋃ i, {x : openFiber f U c | (g.edist (incl (o i)) (incl x)).toReal ∈ Icc (113 * s i / 96) (19 * s i / 16)}) ∪
        ⋃ i, (incl ⁻¹' g.ball (incl (q i)) (R i)))
    (hordinary : ∀ i,
      (∫ x in {x : openFiber f U c | (g.edist (incl (o i)) (incl x)).toReal ∈ Icc (113 * s i / 96) (19 * s i / 16)},
        max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤ C₀ i + D₀ i *
        ∫ x in {x : openFiber f U c | (g.edist (incl (o i)) (incl x)).toReal ∈ Icc (s i / 2) (3 * s i)}, K x ∂gL.volumeMeasure)
    (hbound : ∀ i, ∀ r : ℝ, 0 < r → 2 * a i ≤ r → r ≤ r₀ i →
      (∫ x in {x : openFiber f U c | (g.edist (incl (q i)) (incl x)).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤ C i * (r ^ d +
        ∫ x in {x : openFiber f U c | (g.edist (incl (q i)) (incl x)).toReal ∈ Icc (r / 2) (3 * r)}, K x ∂gL.volumeMeasure)),
    (∫ x in (incl ⁻¹' g.ball (incl p) 1) \ ⋃ i, (incl ⁻¹' g.ball (incl (q i)) (4 * a i)),
      max 0 (D.scalarCurvature x) ∂gL.volumeMeasure) ≤
        (∑ i, C₀ i) + (∑ i, C i * r₀ i ^ d / (1 - (227 / 228 : ℝ) ^ d)) +
          ((∑ i, D₀ i) + (L : ℝ) * ∑ i, C i) * ∫ x in W, K x ∂gL.volumeMeasure := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  dsimp only
  intro D ι κ _ _ o s C₀ D₀ q a r₀ R C d hm hs hRn hMainBall hOrdBall hCritBall
    ha hr₀ hR hC hd W K hW hKi hKn L hL hD₀ hOrdBuffer hCritBuffer hcover hordinary hbound
  let : ConnectedSpace M := { toNonempty := ⟨incl p⟩ }
  let := g.toMetricSpace
  let : MetricSpace (openFiber f U c) :=
    (isEmbedding_openFiberIncl f U c).comapMetricSpace incl
  have hdist (x y : openFiber f U c) :
      dist x y = (g.edist (incl x) (incl y)).toReal := rfl
  have hballEq (x : openFiber f U c) (r : ℝ) :
      incl ⁻¹' g.ball (incl x) r = Metric.ball x r := by
    rw [← g.toMetricSpace_ball]
    rfl
  have hcpt (x : openFiber f U c) (r : ℝ) (hr : 0 ≤ r)
      (hball : ∀ y, g.edist (incl x) y ≤ ENNReal.ofReal r → y ∈ U) :
      IsCompact (Metric.closedBall x r : Set (openFiber f U c)) := by
    have hh := g.isCompact_openFiber_preimage_closedBall hc hf.continuous U c (incl x) r hball
    convert hh using 1
    ext z
    change dist z x ≤ r ↔ g.edist (incl x) (incl z) ≤ ENNReal.ofReal r
    rw [dist_comm, hdist]
    constructor
    · intro hz
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top (incl x) (incl z))]
      exact ENNReal.ofReal_le_ofReal hz
    · exact ENNReal.toReal_le_of_le_ofReal hr
  have hint (x : openFiber f U c) (r : ℝ) (hr : 0 ≤ r)
      (hball : ∀ y, g.edist (incl x) y ≤ ENNReal.ofReal r → y ∈ U) :
      IntegrableOn (fun z => max 0 (D.scalarCurvature z))
        (Metric.closedBall x r) gL.volumeMeasure :=
    (continuous_const.max D.continuous_scalarCurvature).continuousOn.integrableOn_compact
      (hcpt x r hr hball)
  let E := (incl ⁻¹' g.ball (incl p) 1) \ ⋃ i, (incl ⁻¹' g.ball (incl (q i)) (4 * a i))
  let A := fun i => {x : openFiber f U c | (g.edist (incl (o i)) (incl x)).toReal ∈
    Icc (113 * s i / 96) (19 * s i / 16)}
  let B := fun i => (incl ⁻¹' g.ball (incl (q i)) (R i)) \ (incl ⁻¹' g.ball (incl (q i)) (4 * a i))
  let T : κ ⊕ ι → Set (openFiber f U c) := Sum.elim A B
  let h : openFiber f U c → ℝ := fun x => max 0 (D.scalarCurvature x)
  have hmeas (x : openFiber f U c) (r : ℝ) :
      MeasurableSet (incl ⁻¹' g.ball (incl x) r) := by
    rw [hballEq]
    exact Metric.isOpen_ball.measurableSet
  have hcont : Continuous h := continuous_const.max D.continuous_scalarCurvature
  have hEm : MeasurableSet E := (hmeas p 1).diff
    (MeasurableSet.iUnion (fun i => hmeas (q i) (4 * a i)))
  have hAm (i : κ) : MeasurableSet (A i) := by
    change MeasurableSet {x : openFiber f U c | dist (o i) x ∈ Icc _ _}
    exact (isClosed_Icc.preimage (continuous_const.dist continuous_id)).measurableSet
  have hBm (i : ι) : MeasurableSet (B i) :=
    (hmeas (q i) (R i)).diff (hmeas (q i) (4 * a i))
  have hEi : IntegrableOn h E gL.volumeMeasure := by
    apply (hint p 1 (by norm_num) hMainBall).mono_set
    intro x hx
    exact Metric.ball_subset_closedBall (by simpa only [hballEq] using hx.1)
  have hAi (i : κ) : IntegrableOn h (A i) gL.volumeMeasure := by
    apply (hint (o i) (3*s i) (mul_nonneg (by norm_num) (hs i)) (hOrdBall i)).mono_set
    intro x hx
    change dist (o i) x ∈ Icc _ _ at hx
    rw [Metric.mem_closedBall, dist_comm]
    linarith [hs i, hx.2]
  have hBi (i : ι) : IntegrableOn h (B i) gL.volumeMeasure := by
    apply (hint (q i) (3*r₀ i) (mul_nonneg (by norm_num) (hr₀ i).le) (hCritBall i)).mono_set
    intro x hx
    have hx' : dist (q i) x < R i := by
      simpa only [hballEq, Metric.mem_ball, dist_comm] using hx.1
    rw [Metric.mem_closedBall, dist_comm]
    linarith [hR i, hr₀ i]
  have hTm (i : κ ⊕ ι) : MeasurableSet (T i) := by
    cases i with
    | inl i => exact hAm i
    | inr i => exact hBm i
  have hTi (i : κ ⊕ ι) : IntegrableOn h (T i) gL.volumeMeasure := by
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
  have hord (i : κ) : (∫ x in A i, h x ∂gL.volumeMeasure) ≤
      C₀ i + D₀ i * ∫ x in W, K x ∂gL.volumeMeasure := by
    apply (hordinary i).trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (hD₀ i)
    exact setIntegral_mono_set hKi (Filter.Eventually.of_forall hKn)
      (Filter.Eventually.of_forall (hOrdBuffer i))
  have hcrit (i : ι) :=
    g.integral_openFiber_pos_scalar_outside_ambient_ball_le_of_nonneg hc hf U hreg c (q i)
      hm (ha i) (hr₀ i) (hRn i) (hR i) (hC i) hd hL (hCritBall i)
      D W K hW hKi hKn (hCritBuffer i) (hbound i)
  calc
    _ ≤ (∑ i, (C₀ i + D₀ i * ∫ x in W, K x ∂gL.volumeMeasure)) +
        ∑ i, (C i * r₀ i ^ d / (1 - (227 / 228 : ℝ) ^ d) +
          C i * (L : ℝ) * ∫ x in W, K x ∂gL.volumeMeasure) :=
      add_le_add (Finset.sum_le_sum fun i _ => hord i)
        (Finset.sum_le_sum fun i _ => hcrit i)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]; ring
