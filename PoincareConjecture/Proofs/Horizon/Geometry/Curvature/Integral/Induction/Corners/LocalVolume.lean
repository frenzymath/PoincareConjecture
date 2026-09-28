import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixSliceVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.EmptyPrefix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 800000 in
private theorem PoincareConjecture.RiemannianMetric.strainer_volume_iterate
    {n m k : ℕ} (hdim : n = m + k) {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (f : Fin k → M → ℝ)
    (w : ∀ x : M, Fin k → TangentSpace (𝓡 n) x)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1))) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i, g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (w x i) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (w x i) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i v, D.hessian (f i) x v v ≤ C * g.inner x v v)
    (p : M) {r R T : ℝ} (hr : 0 ≤ r) (hT : 0 < T)
    (hroom : r + 2 * T * ((k : ℝ) + 1) ≤ R)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal R → y ∈ U) :
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 n) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective
        (mfderiv (𝓡 n) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m + k) :=
          ⟨by rw [finrank_euclideanSpace_fin, hdim]⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let gL := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
          (openFiberIncl F U c) (contMDiff_openFiberIncl (m := m) hF U hreg c)
          (injective_mfderiv_openFiberIncl (m := m) hF U hreg c)
        (PoincareConjecture.RiemannianMetric.volumeMeasure gL).real
            {y | g.edist p (openFiberIncl F U c y) ≤ ENNReal.ofReal r} ≤
          (1 / T) ^ k * Real.exp (8 * (n : ℝ) * C * T * k) *
            g.volumeMeasure.real {y | g.edist p y ≤ ENNReal.ofReal (r + 2 * T * k)} := by
  classical
  induction k generalizing n m r with
  | zero =>
    have hdim' : m = n := by omega
    subst hdim'
    let F := fun y (i : Fin 0) => f i y
    let hF : ContMDiff (𝓡 m) 𝓘(ℝ, Fin 0 → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    have hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 m) 𝓘(ℝ, Fin 0 → ℝ) F x) := by
      intro x hx a
      refine ⟨0, ?_⟩
      apply funext
      intro i
      exact Fin.elim0 i
    refine ⟨hreg, ?_⟩
    intro c
    have hrR : r ≤ R := by push_cast at hroom; linarith
    have hSU : {y | g.edist p y ≤ ENNReal.ofReal r} ⊆ U := by
      intro y hy
      exact hball y (hy.trans (ENNReal.ofReal_le_ofReal hrR))
    have heq := g.openFiber_zero_volume_real_preimage_of_isCompact hF U hreg c
      (g.isCompact_closedBall_of_metricComplete hc p r) hSU
    simpa only [Nat.cast_zero, pow_zero, mul_zero, add_zero, Real.exp_zero, one_mul,
      Set.mem_ofPred_eq, F, PoincareConjecture.RiemannianMetric.openRegularFiberMetric] using heq.le
  | succ k ih =>
    have hdim' : n = (m + 1) + k := by omega
    subst hdim'
    have hsmall' : δ ≤ 1 / (8 * ((k : ℝ) + 1)) := hsmall.trans
      (one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
    have hroom' : r + 4 * T ≤ R := by
      push_cast at hroom
      nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    obtain ⟨hprefix, hfull, hstep⟩ :=
      g.strainer_prefix_volume_le_on_ambient_closedBall (d := m) (k := k) D hc f w hf U
        hδ hsmall' hC hunit hopposite hcross htight hH p hr hT hroom' hball
    obtain ⟨hprevreg, hprev⟩ := ih (m := m + 1) rfl g D hc
      (fun i : Fin k => f i.castSucc) (fun x i => w x i.castSucc)
      (fun i => hf i.castSucc) hsmall'
      (fun x hx i => hunit x hx i.castSucc)
      (fun x hx i => hopposite x hx i.castSucc)
      (fun x hx i j hij => hcross x hx _ _ (fun h => hij (Fin.castSucc_inj.mp h)))
      (fun x hx i j hij => htight x hx _ _ (fun h => hij (Fin.castSucc_inj.mp h)))
      (fun x hx i v => hH x hx i.castSucc v)
      (r := r + 2 * T) (by positivity)
      (by push_cast at hroom; nlinarith) hball
    refine ⟨hfull, ?_⟩
    intro c
    let P := fun y (i : Fin k) => f i.castSucc y
    let hP : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
      contMDiff_pi_space.mpr (fun i => hf i.castSucc)
    let cP := fun i : Fin k => c i.castSucc
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
    let := openFiberChartedSpace (m := m + 1) hP U hprefix cP
    let := isManifold_openFiber (m := m + 1) hP U hprefix cP
    let gP := g.openRegularFiberMetric hP U hprefix cP
    have hi : gP.volumeMeasure.real
        {y | g.edist p (openFiberIncl P U cP y) ≤ ENNReal.ofReal (r + 2 * T)} ≤
        (1 / T) ^ k * Real.exp (8 * (((m + 1) + k : ℕ) : ℝ) * C * T * k) *
          g.volumeMeasure.real
            {y | g.edist p y ≤ ENNReal.ofReal (r + 2 * T + 2 * T * k)} := hprev cP
    have hm := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ Real.exp (8 * (m : ℝ) * C * T) / T by positivity)
    refine (hstep c).trans (hm.trans ?_)
    have hrad : r + 2 * T + 2 * T * k = r + 2 * T * ((k + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hrad]
    have hexp : 8 * (m : ℝ) * C * T +
        8 * (((m + 1) + k : ℕ) : ℝ) * C * T * k ≤
        8 * (((m + 1) + k : ℕ) : ℝ) * C * T * ((k + 1 : ℕ) : ℝ) := by
      have hn : (m : ℝ) ≤ ((m + 1 + k : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ m + 1 + k)
      have hh := mul_le_mul_of_nonneg_right hn (show 0 ≤ 8 * C * T by positivity)
      push_cast at *
      nlinarith only [hh]
    have he := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
        (show 0 ≤ (1 / T) ^ (k + 1) by positivity))
      (show 0 ≤ g.volumeMeasure.real
        {y | g.edist p y ≤ ENNReal.ofReal (r + 2 * T * ((k + 1 : ℕ) : ℝ))} from
        ENNReal.toReal_nonneg)
    convert he using 1
    rw [Real.exp_add, pow_succ]
    ring

theorem PoincareConjecture.RiemannianMetric.strainer_openFiber_volume_le_on_ambient_closedBall
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (f : Fin k → M → ℝ)
    (w : ∀ x : M, Fin k → TangentSpace (𝓡 (m + k)) x)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1))) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i, g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (w x i) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (w x i) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i v, D.hessian (f i) x v v ≤ C * g.inner x v v)
    (p : M) {r : ℝ} (hr : 0 < r)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal (3 * r / 2) → y ∈ U) :
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective
        (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let gL := g.openRegularFiberMetric hF U hreg c
        gL.volumeMeasure.real
            {y | g.edist p (openFiberIncl F U c y) ≤ ENNReal.ofReal r} ≤
          (4 * ((k : ℝ) + 1) / r) ^ k *
            Real.exp (2 * ((m + k : ℕ) : ℝ) * C * r) *
            g.volumeMeasure.real {y | g.edist p y ≤ ENNReal.ofReal (3 * r / 2)} := by
  classical
  let T := r / (4 * ((k : ℝ) + 1))
  have hT : 0 < T := by dsimp [T]; positivity
  have hTr : 4 * ((k : ℝ) + 1) * T = r := by
    dsimp [T]
    field_simp
  have hroom : r + 2 * T * ((k : ℝ) + 1) ≤ 3 * r / 2 := by nlinarith only [hTr]
  obtain ⟨hreg, hvol⟩ := PoincareConjecture.RiemannianMetric.strainer_volume_iterate
    (m := m) rfl g D hc f w hf U hδ hsmall hC hunit hopposite hcross htight hH
    p hr.le hT hroom hball
  refine ⟨hreg, ?_⟩
  intro c
  refine (hvol c).trans ?_
  have hbase : 1 / T = 4 * ((k : ℝ) + 1) / r := by
    dsimp [T]
    field_simp
  have hrad : r + 2 * T * k ≤ 3 * r / 2 := by nlinarith only [hTr, hT]
  have hmeasure : g.volumeMeasure.real
      {y | g.edist p y ≤ ENNReal.ofReal (r + 2 * T * k)} ≤
      g.volumeMeasure.real {y | g.edist p y ≤ ENNReal.ofReal (3 * r / 2)} := by
    apply ENNReal.toReal_mono
      (g.isCompact_closedBall_of_metricComplete hc p (3 * r / 2)).measure_ne_top
    apply measure_mono
    intro y hy
    exact hy.trans (ENNReal.ofReal_le_ofReal hrad)
  have he : 8 * ((m + k : ℕ) : ℝ) * C * T * k ≤
      2 * ((m + k : ℕ) : ℝ) * C * r := by
    have hh := mul_le_mul_of_nonneg_left
      (show 4 * T * k ≤ r by nlinarith only [hTr, hT])
      (show 0 ≤ 2 * ((m + k : ℕ) : ℝ) * C by positivity)
    nlinarith only [hh]
  rw [hbase]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity))
    hmeasure ENNReal.toReal_nonneg (by positivity)
