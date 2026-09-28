import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixPair
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.PrefixFiber
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberCompact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelCompactDistance

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology Bundle

set_option maxHeartbeats 600000 in

theorem PoincareConjecture.RiemannianMetric.strainer_prefix_edist_le_of_ambient_closedBall
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 1) + k))) M]
    [IsManifold (𝓡 ((m + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((m + 1) + k) M) (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (f h : Fin (k + 1) → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (h i))
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
    let P := fun y (i : Fin k) => f i.castSucc y
    let hP : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
      contMDiff_pi_space.mpr (fun i => hf i.castSucc)
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hprefix : ∀ x ∈ U, Surjective
        (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) P x),
      ∃ hfull : ∀ x ∈ U, Surjective
          (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) F x),
        ∀ c : Fin (k + 1) → ℝ,
          let cP := fun i : Fin k => c i.castSucc
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
            (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
          letI := openFiberChartedSpace (m := m + 1) hP U hprefix cP
          letI := isManifold_openFiber (m := m + 1) hP U hprefix cP
          let gP := g.openRegularFiberMetric hP U hprefix cP
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
            m + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
          letI := openFiberChartedSpace (m := m) hF U hfull c
          letI := isManifold_openFiber (m := m) hF U hfull c
          let gFull := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
            (openFiberIncl F U c) (contMDiff_openFiberIncl (m := m) hF U hfull c)
            (injective_mfderiv_openFiberIncl (m := m) hF U hfull c)
          let proj : openFiber F U c → openFiber P U cP :=
            fun x => ⟨x.1, funext (fun i => congrFun x.2 i.castSucc)⟩
          ∀ x y : openFiber F U c,
            (∀ z, g.edist (openFiberIncl F U c x) z ≤ ENNReal.ofReal (40*r) → z ∈ U) →
            gP.edist (proj x) (proj y) < ENNReal.ofReal r →
            PoincareConjecture.RiemannianMetric.edist gFull x y ≤
              ENNReal.ofReal (9 * Real.exp (128*C*r)) * gP.edist (proj x) (proj y) ∧
              Joined x y := by
  classical
  let P := fun y (i : Fin k) => f i.castSucc y
  let hP : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
    contMDiff_pi_space.mpr (fun i => hf i.castSucc)
  let F := fun y i => f i y
  let hF : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F :=
    contMDiff_pi_space.mpr hf
  obtain ⟨hG, _, hprefix, hbounds⟩ := g.strainer_prefix_openFiber_opposite_bounds
    D f h hf hh U hδ hsmall hC hunit hopposite hcross htight hH
  let a := 2 * ((k : ℝ) + 1) * δ
  let G := fun x => (1-a)*h (Fin.last k) x +
    (a/((k:ℝ)+1))*∑ i : Fin k, h i.castSucc x
  have hsmall' : δ ≤ 1 / (8 * (((k+1:ℕ):ℝ)+1)) := hsmall.trans
    (one_div_le_one_div_of_le (by positivity) (by
      have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
      push_cast
      nlinarith [sq_nonneg (k:ℝ)]))
  have hnum := Poincare.CurvatureIntegral.strainer_parameter_bounds (k+1) hδ hsmall'
  have hfull : ∀ x ∈ U, Surjective
      (mfderiv (𝓡 ((m+1)+k)) 𝓘(ℝ, Fin (k+1) → ℝ) F x) := by
    intro x hx b
    have hs := (g.strainer_gradients_regular f x (fun i => g.gradient (h i) x)
      hδ hnum.1 (by simpa using hnum.2) (fun i => (hunit x hx i).2)
      (hopposite x hx) (fun i j hij => (hcross x hx i j hij).1)).2
    obtain ⟨v, hv⟩ := hs b
    refine ⟨v, ?_⟩
    apply funext
    intro i
    rw [Poincare.Geometry.Manifold.mfderiv_pi_apply f hf]
    exact congrFun hv i
  refine ⟨hprefix, hfull, ?_⟩
  intro c
  let cP := fun i : Fin k => c i.castSucc
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+1)+k))) = (m+1)+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let (v : Fin k → ℝ) := openFiberChartedSpace (m := m+1) hP U hprefix v
  let (v : Fin k → ℝ) := isManifold_openFiber (m := m+1) hP U hprefix v
  have hlast : ∀ v : Fin k → ℝ, ∀ x : openFiber P U v,
      mfderiv (𝓡 (m+1)) 𝓘(ℝ,ℝ) (f (Fin.last k) ∘ openFiberIncl P U v) x ≠ 0 := by
    intro v x
    apply ((g.openRegularFiberMetric hP U hprefix v).tangentNorm_gradient_pos_iff _ x).mp
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) ((hbounds v).2.2 x).1.1
  let gP := g.openRegularFiberMetric hP U hprefix cP
  let φ := f (Fin.last k) ∘ openFiberIncl P U cP
  let ψ := G ∘ openFiberIncl P U cP
  have hφ : ContMDiff (𝓡 (m+1)) 𝓘(ℝ,ℝ) ∞ φ := (hbounds cP).1
  have hψ : ContMDiff (𝓡 (m+1)) 𝓘(ℝ,ℝ) ∞ ψ := (hbounds cP).2.1
  have hpairdata := (hbounds cP).2.2
  obtain ⟨hlevel, e, hambient, hedist⟩ :=
    g.exists_prefix_openFiber_metric_equivalence f hf U hprefix hfull hlast c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+1)+k))) = m+(k+1)) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let := openFiberChartedSpace (m := m) hF U hfull c
  let := isManifold_openFiber (m := m) hF U hfull c
  let gFull := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
    (openFiberIncl F U c) (contMDiff_openFiberIncl (m := m) hF U hfull c)
    (injective_mfderiv_openFiberIncl (m := m) hF U hfull c)
  let proj : openFiber F U c → openFiber P U cP :=
    fun x => ⟨x.1, funext (fun i => congrFun x.2 i.castSucc)⟩
  dsimp only
  intro x y hball hxy
  have hincl : ContMDiff (𝓡 (m+1)) (𝓡 ((m+1)+k)) ∞ (openFiberIncl P U cP) :=
    contMDiff_openFiberIncl (m := m+1) hP U hprefix cP
  have hdist (v w : openFiber P U cP) :
      g.edist (openFiberIncl P U cP v) (openFiberIncl P U cP w) ≤ gP.edist v w :=
    PoincareConjecture.RiemannianMetric.edist_map_le_of_metric_pullback gP g hincl
      (PoincareConjecture.RiemannianMetric.openRegularFiberMetric_inner hP U hprefix cP g) v w
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m+1)) : openFiber P U cP → Type _) :=
    ⟨gP.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m+1)))
      (TangentSpace (𝓡 (m+1)) : openFiber P U cP → Type _) :=
    ⟨⟨gP.inner, gP.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (openFiber P U cP) :=
    EMetricSpace.ofRiemannianMetric (𝓡 (m+1)) (openFiber P U cP)
  have hcompact : IsCompact {z | gP.edist (proj x) z ≤ ENNReal.ofReal (40*r)} := by
    apply (g.isCompact_openFiber_preimage_closedBall hc hP.continuous U cP
      (openFiberIncl F U c x) (40*r) hball).of_isClosed_subset
      (isClosed_le (continuous_const.edist continuous_id) continuous_const)
    intro z hz
    exact (hdist (proj x) z).trans hz
  obtain ⟨hreglevel, hlocal⟩ :=
    gP.leviCivitaData.regularLevel_edist_le_of_opposite_gradients_of_isCompact_closedBall
      hφ hψ ⊤ (by positivity : 0≤2*C) hr
      (fun z _ => (hpairdata z).1) (fun z _ => (hpairdata z).2.1)
      (fun z _ => by
        simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient, neg_div]
          using (hpairdata z).2.2.1)
      (fun z _ v _ => ((hpairdata z).2.2.2 v).1)
      (fun z _ v _ => ((hpairdata z).2.2.2 v).2)
      (proj x) hcompact (subset_univ _)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1))) = m+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hφ ⊤ (fun x _ => hlevel x) m (c (Fin.last k))
  let := isManifold_openLevelSet hφ ⊤ (fun x _ => hlevel x) m (c (Fin.last k))
  have heproj (z : openFiber F U c) :
      openLevelIncl φ ⊤ (c (Fin.last k)) (e.symm z) = proj z := by
    apply (isEmbedding_openFiberIncl P U cP).injective
    rw [← hambient, e.apply_symm_apply]
    rfl
  have hxball : openLevelIncl φ ⊤ (c (Fin.last k)) (e.symm x) ∈ gP.ball (proj x) r := by
    rw [heproj]
    change gP.edist (proj x) (proj x) < ENNReal.ofReal r
    rw [show gP.edist (proj x) (proj x) = 0 from Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hyball : openLevelIncl φ ⊤ (c (Fin.last k)) (e.symm y) ∈ gP.ball (proj x) r := by
    rw [heproj]
    exact hxy
  have he := hlocal (c (Fin.last k)) (e.symm x) (e.symm y) hxball hyball
  constructor
  · rw [← hedist, e.apply_symm_apply, e.apply_symm_apply, heproj, heproj] at he
    simpa only [show 64 * (2*C) * r = 128*C*r by ring] using he.1
  · simpa only [e.apply_symm_apply] using he.2.map e.continuous
