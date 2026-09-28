import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.EmptyFiberDistance







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle

set_option maxHeartbeats 800000 in
private theorem PoincareConjecture.RiemannianMetric.strainer_distance_iterate
    {n m k : ℕ} (hdim : n = m+k) {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (256 * ((k : ℝ) + 1) ^ 2)) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i,
      g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (g.gradient (h i) x) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (g.gradient (h i) x) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ ∧
      |g.inner x (g.gradient (h i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i w,
      D.hessian (f i) x w w ≤ C * g.inner x w w ∧
      D.hessian (h i) x w w ≤ C * g.inner x w w) {r : ℝ} (hr : 0 < r) :
    let A := 9 * Real.exp (128*C*r)
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 n) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m+k) :=
          ⟨by rw [finrank_euclideanSpace_fin, hdim]⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let gL := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
          (openFiberIncl F U c) (contMDiff_openFiberIncl (m := m) hF U hreg c)
          (injective_mfderiv_openFiberIncl (m := m) hF U hreg c)
        let incl := openFiberIncl F U c
        ∀ x y : openFiber F U c,
          (∀ z, g.edist (incl x) z ≤ ENNReal.ofReal (40*r) → z ∈ U) →
          ENNReal.ofReal (A^k) * g.edist (incl x) (incl y) < ENNReal.ofReal r →
          PoincareConjecture.RiemannianMetric.edist gL x y ≤ ENNReal.ofReal (A^k) * g.edist (incl x) (incl y) ∧ Joined x y := by
  classical
  induction k generalizing n m with
  | zero =>
    have hdim' : m = n := by omega
    subst hdim'
    let F := fun y (i : Fin 0) => f i y
    let hF : ContMDiff (𝓡 m) 𝓘(ℝ, Fin 0 → ℝ) ∞ F := contMDiff_pi_space.mpr hf
    have hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 m) 𝓘(ℝ, Fin 0 → ℝ) F x) := by
      intro x hx b
      refine ⟨0, ?_⟩
      exact funext (fun i => Fin.elim0 i)
    refine ⟨hreg, ?_⟩
    intro c
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m+0) :=
      ⟨by simp⟩
    let := openFiberChartedSpace (m := m) hF U hreg c
    let := isManifold_openFiber (m := m) hF U hreg c
    let gL := g.openRegularFiberMetric (m := m) (k := 0) hF U hreg c
    let incl := openFiberIncl F U c
    dsimp only
    intro x y hball hxy
    have hgap : g.edist (incl x) (incl y) < ENNReal.ofReal r := by
      simpa only [pow_zero, ENNReal.ofReal_one, one_mul] using hxy
    have hsmallball : ∀ z, g.edist (incl x) z ≤ ENNReal.ofReal (3*r) → z ∈ U :=
      fun z hz => hball z (hz.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hx : incl x ∈ g.ball (incl x) r := by
      change g.edist (incl x) (incl x) < ENNReal.ofReal r
      rw [show g.edist (incl x) (incl x) = 0 from Manifold.riemannianEDist_self]
      exact ENNReal.ofReal_pos.mpr hr
    have he := g.openFiber_zero_edist_eq_of_ambient_closedBall hc hF U hreg c
      (incl x) hr hsmallball x y hx hgap
    constructor
    · simpa only [pow_zero, ENNReal.ofReal_one, one_mul,
        PoincareConjecture.RiemannianMetric.openRegularFiberMetric] using he.le
    · let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : openFiber F U c → Type _) :=
        ⟨gL.toRiemannianMetric⟩
      have hfinite : gL.edist x y < ⊤ := he.trans_lt (hgap.trans ENNReal.ofReal_lt_top)
      obtain ⟨γ,hγ0,hγ1,hγ,_⟩ := Manifold.exists_lt_of_riemannianEDist_lt hfinite
      exact ⟨Path.ofLine hγ.continuousOn hγ0 hγ1⟩
  | succ k ih =>
    have hdim' : n = (m+1)+k := by omega
    subst hdim'
    have hsmall' : δ ≤ 1 / (256*((k:ℝ)+1)^2) := hsmall.trans
      (one_div_le_one_div_of_le (by positivity) (by
        have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
        push_cast
        nlinarith))
    obtain ⟨hprefix,hfull,hstep⟩ := g.strainer_prefix_edist_le_of_ambient_closedBall
      D hc f h hf hh U hδ hsmall' hC hunit hopposite hcross htight hH hr
    obtain ⟨hprevreg,hprev⟩ := ih (m := m+1) rfl g D hc
      (fun i : Fin k => f i.castSucc) (fun i : Fin k => h i.castSucc)
      (fun i => hf i.castSucc) (fun i => hh i.castSucc) hsmall'
      (fun x hx i => hunit x hx i.castSucc)
      (fun x hx i => hopposite x hx i.castSucc)
      (fun x hx i j hij => hcross x hx _ _ (fun h => hij (Fin.castSucc_inj.mp h)))
      (fun x hx i j hij => htight x hx _ _ (fun h => hij (Fin.castSucc_inj.mp h)))
      (fun x hx i w => hH x hx i.castSucc w)
    refine ⟨hfull, ?_⟩
    intro c
    let P := fun y (i : Fin k) => f i.castSucc y
    let hP : ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
      contMDiff_pi_space.mpr (fun i => hf i.castSucc)
    let cP := fun i : Fin k => c i.castSucc
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ, Fin (k+1) → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+1)+k))) = (m+1)+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    let := openFiberChartedSpace (m := m+1) hP U hprefix cP
    let := isManifold_openFiber (m := m+1) hP U hprefix cP
    let gP := g.openRegularFiberMetric hP U hprefix cP
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+1)+k))) = m+(k+1)) :=
      ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
    let := openFiberChartedSpace (m := m) hF U hfull c
    let := isManifold_openFiber (m := m) hF U hfull c
    let proj : openFiber F U c → openFiber P U cP :=
      fun x => ⟨x.1, funext (fun i => congrFun x.2 i.castSucc)⟩
    let A := 9 * Real.exp (128*C*r)
    have hA : 1 ≤ A := by
      have hh := Real.one_le_exp (show 0≤128*C*r by positivity)
      dsimp only [A]
      linarith
    have hAp : 0 ≤ A^k := pow_nonneg (by linarith) k
    dsimp only
    intro x y hball hxy
    have hpows : A^k ≤ A^(k+1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right hAp hA
    have hgap : ENNReal.ofReal (A^k) *
        g.edist (openFiberIncl F U c x) (openFiberIncl F U c y) < ENNReal.ofReal r :=
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hpows) le_rfl).trans_lt hxy
    have hprevious := hprev cP (proj x) (proj y) hball hgap
    have hclose : gP.edist (proj x) (proj y) < ENNReal.ofReal r :=
      hprevious.1.trans_lt hgap
    have hnext := hstep c x y hball hclose
    refine ⟨hnext.1.trans ?_, hnext.2⟩
    have hmul := mul_le_mul' (show ENNReal.ofReal A ≤ ENNReal.ofReal A from le_rfl) hprevious.1
    have hm : ENNReal.ofReal A * gP.edist (proj x) (proj y) ≤
        ENNReal.ofReal A * (ENNReal.ofReal (A^k) *
          g.edist (openFiberIncl F U c x) (openFiberIncl F U c y)) := hmul
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith : 0≤A), ← pow_succ'] at hm
    exact hm



theorem PoincareConjecture.RiemannianMetric.strainer_openFiber_edist_le_of_ambient_closedBall
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M) (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (h i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (256 * ((k : ℝ) + 1) ^ 2)) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i,
      g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (g.gradient (h i) x) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (g.gradient (h i) x) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ ∧
      |g.inner x (g.gradient (h i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i w,
      D.hessian (f i) x w w ≤ C * g.inner x w w ∧
      D.hessian (h i) x w w ≤ C * g.inner x w w) {r : ℝ} (hr : 0 < r) :
    let A := 9 * Real.exp (128*C*r)
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let gL := g.openRegularFiberMetric hF U hreg c
        let incl := openFiberIncl F U c
        ∀ x y : openFiber F U c,
          (∀ z, g.edist (incl x) z ≤ ENNReal.ofReal (40*r) → z ∈ U) →
          ENNReal.ofReal (A^k) * g.edist (incl x) (incl y) < ENNReal.ofReal r →
          gL.edist x y ≤ ENNReal.ofReal (A^k) * g.edist (incl x) (incl y) ∧ Joined x y := by
  simpa only [PoincareConjecture.RiemannianMetric.openRegularFiberMetric] using
    g.strainer_distance_iterate (m := m) rfl D hc f h hf hh U hδ hsmall hC
      hunit hopposite hcross htight hH hr
