import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.LocalSmoothMinimizingInterpolator
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.SideGeodesic













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture

open M63





theorem m64_exists_local_unit_geodesic_uniqueness
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p0 : M) :
    ∃ O : Set M, IsOpen O ∧ p0 ∈ O ∧
      ∀ p ∈ O, ∀ q ∈ O, ∀ gamma eta : ℝ → M,
        g.IsGeodesicOn gamma (Icc (0 : ℝ) 1) →
        g.IsGeodesicOn eta (Icc (0 : ℝ) 1) →
        gamma 0 = p → eta 0 = p → gamma 1 = q → eta 1 = q →
        g.tangentNorm (gamma 0) (curveVelocity gamma 0) = (g.edist p q).toReal →
        g.tangentNorm (eta 0) (curveVelocity eta 0) = (g.edist p q).toReal →
        EqOn gamma eta (Icc (0 : ℝ) 1) := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p0
  let x0 : E := c p0
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := g.pullbackCoefficients c.symm
  have hc0 : p0 ∈ c.source := mem_extChartAt_source p0
  have hx0 : x0 ∈ c.target := c.map_source hc0
  have hcopen : IsOpen c.source := isOpen_extChartAt_source p0
  have htopen : IsOpen c.target := isOpen_extChartAt_target p0
  have hB : ContDiffOn ℝ ∞ B c.target := g.contDiffOn_chartCoefficients p0
  obtain ⟨e, he0, he00, _hsource, _htarget, _he, hei, hefirst,
      Gamma, hGamma, hspec⟩ :=
    exists_joint_coordinate_exponential_inverse htopen hB
      (fun y hy => g.isInvertible_chartCoefficients p0 hy)
      (fun y _ v w => g.symm _ _ _) hx0
  obtain ⟨eta, heta, hetaSub⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  have hbox {y v : E} (hy : y ∈ ball x0 eta) (hv : v ∈ ball 0 eta) :
      (y, v) ∈ e.source := by
    apply hetaSub
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using And.intro hy hv
  let curve : (E × E) → ℝ → M := fun z t => c.symm (Gamma (z, t)).1
  have hcurve (z : E × E) (hz : z ∈ e.source) :
      g.IsGeodesicOn (curve z) (Ioo (-2 : ℝ) 2) := by
    apply g.isGeodesicOn_chart_curve p0 isOpen_Ioo
      (q := fun t => (Gamma (z, t)).1) (w := fun t => (Gamma (z, t)).2)
    intro t ht
    have hd := (hspec z hz).2.2 t ht
    refine ⟨hd.1, ?_, ?_⟩
    · simpa [coordinateGeodesicField] using hd.2.hasFDerivAt.fst.hasDerivAt
    · simpa +instances [B, c, coordinateGeodesicField] using!
        hd.2.hasFDerivAt.snd.hasDerivAt
  have hcurve0 (z : E × E) (hz : z ∈ e.source) :
      curve z 0 = c.symm z.1 := by
    dsimp only [curve]
    rw [(hspec z hz).1]
  have hcurve1 (z : E × E) (hz : z ∈ e.source) :
      curve z 1 = c.symm (e z).2 := by
    dsimp only [curve]
    rw [(hspec z hz).2.1]
  have hcurveDeriv (z : E × E) (hz : z ∈ e.source) :
      HasDerivAt (fun t => c (curve z t)) z.2 0 := by
    have hd : HasDerivAt (fun t => (Gamma (z, t)).1) z.2 0 := by
      simpa [(hspec z hz).1, coordinateGeodesicField] using
        ((hspec z hz).2.2 0 (by norm_num)).2.hasFDerivAt.fst.hasDerivAt
    have heq : (fun t => c (curve z t)) =ᶠ[𝓝 0] fun t => (Gamma (z, t)).1 := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-2) 2 by norm_num)]
        with t ht
      exact c.right_inv ((hspec z hz).2.2 t ht).1
    exact hd.congr_of_eventuallyEq heq

  have hcSymm : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm x0 :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p0).contMDiffAt
      (htopen.mem_nhds hx0)
  have hcinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) c.symm x0) := by
    simpa only [c, modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) (x := p0) hx0).injective
  obtain ⟨A, hA, _hdet⟩ := g.exists_frozenPullbackEquiv hcinj
  have hnear := g.eventually_pullbackNorm_bounds hcSymm A hA
    (ε := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨V, hVsub, hVopen, hV0⟩ := _root_.mem_nhds_iff.mp hnear
  let C : ℝ := 2 * (‖A.symm.toContinuousLinearMap‖ + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hnorm (y : E) (hy : y ∈ V) (v : E) :
      ‖v‖ ≤ C * g.tangentNorm (c.symm y) (mfderiv (𝓡 n) (𝓡 n) c.symm y v) := by
    have hlo := (hVsub hy v).1
    have hN : 0 ≤ g.tangentNorm (c.symm y)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y v) := Real.sqrt_nonneg _
    have hhalf : ‖A v‖ ≤ 2 * g.tangentNorm (c.symm y)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y v) := by linarith
    calc
      ‖v‖ = ‖A.symm (A v)‖ := by rw [A.symm_apply_apply]
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A v‖ :=
        A.symm.toContinuousLinearMap.le_opNorm (A v)
      _ ≤ ‖A.symm.toContinuousLinearMap‖ *
          (2 * g.tangentNorm (c.symm y) (mfderiv (𝓡 n) (𝓡 n) c.symm y v)) :=
        mul_le_mul_of_nonneg_left hhalf (norm_nonneg _)
      _ ≤ C * g.tangentNorm (c.symm y) (mfderiv (𝓡 n) (𝓡 n) c.symm y v) := by
        dsimp only [C]
        nlinarith
  have hcAt : ContinuousAt (fun p : M => c p) p0 :=
    continuousAt_extChartAt (I := 𝓡 n) p0
  have hcc : ContinuousAt (fun pq : M × M => (c pq.1, c pq.2)) (p0, p0) :=
    (hcAt.comp continuousAt_fst).prodMk (hcAt.comp continuousAt_snd)
  have het : (x0, x0) ∈ e.target := he00 ▸ e.map_source he0
  obtain ⟨U1, U2, hU1, hpU1, hU2, hpU2, hUV⟩ :=
    mem_nhds_prod_iff'.mp (hcc.preimage_mem_nhds (e.open_target.mem_nhds het))
  have hsmall : {p : M | p ∈ c.source ∧ c p ∈ ball x0 eta ∧ c p ∈ V} ∈ 𝓝 p0 :=
    inter_mem (hcopen.mem_nhds hc0)
      (hcAt.preimage_mem_nhds
        (inter_mem (isOpen_ball.mem_nhds (mem_ball_self heta)) (hVopen.mem_nhds hV0)))
  obtain ⟨W, hWsub, hWopen, hpW⟩ := _root_.mem_nhds_iff.mp hsmall
  let delta : ℝ := min 1 (eta / C) / 4
  have hdelta : 0 < delta := div_pos (lt_min zero_lt_one (div_pos heta hC)) (by norm_num)
  have hd1 : 2 * delta < 1 := by
    have hh := min_le_left (1 : ℝ) (eta / C)
    dsimp only [delta]
    linarith
  have hdeta : C * (2 * delta) < eta := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (eta / C)) hC.le
    have hdiv : C * (eta / C) = eta := by field_simp [hC.ne']
    rw [hdiv] at hh
    dsimp only [delta]
    nlinarith
  let O : Set M := (U1 ∩ U2) ∩ (W ∩ g.ball p0 delta)
  have hballOpen : IsOpen (g.ball p0 delta) := by
    have heq : g.ball p0 delta = Metric.eball p0 (ENNReal.ofReal delta) := by
      ext p
      change (g.edist p0 p < ENNReal.ofReal delta) ↔
        (g.edist p p0 < ENNReal.ofReal delta)
      rw [show g.edist p0 p = g.edist p p0 from Manifold.riemannianEDist_comm]
    rw [heq]
    exact Metric.isOpen_eball
  have hOopen : IsOpen O := (hU1.inter hU2).inter (hWopen.inter hballOpen)
  have hpO : p0 ∈ O := by
    refine ⟨⟨hpU1, hpU2⟩, hpW, ?_⟩
    change g.edist p0 p0 < ENNReal.ofReal delta
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hdelta
  have hOsource {p : M} (hp : p ∈ O) : p ∈ c.source := (hWsub hp.2.1).1
  have hOcoord {p : M} (hp : p ∈ O) : c p ∈ ball x0 eta := (hWsub hp.2.1).2.1
  have hOV {p : M} (hp : p ∈ O) : c p ∈ V := (hWsub hp.2.1).2.2
  have hpqTarget {p q : M} (hp : p ∈ O) (hq : q ∈ O) :
      (c p, c q) ∈ e.target :=
    hUV (show (p, q) ∈ U1 ×ˢ U2 from ⟨hp.1.1, hq.1.2⟩)
  have hpqSmall {p q : M} (hp : p ∈ O) (hq : q ∈ O) :
      g.edist p q < ENNReal.ofReal 1 ∧ C * (g.edist p q).toReal < eta := by
    have hdist : g.edist p q < ENNReal.ofReal (2 * delta) := by
      calc
        g.edist p q ≤ g.edist p p0 + g.edist p0 q :=
          Manifold.riemannianEDist_triangle
        _ < ENNReal.ofReal delta + ENNReal.ofReal delta := ENNReal.add_lt_add
          (by
            rw [show g.edist p p0 = g.edist p0 p from Manifold.riemannianEDist_comm]
            exact hp.2.2) hq.2.2
        _ = ENNReal.ofReal (2 * delta) := by
          rw [← ENNReal.ofReal_add hdelta.le hdelta.le]
          congr 1
          ring
    refine ⟨hdist.trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hd1), ?_⟩
    exact (mul_lt_mul_of_pos_left (ENNReal.toReal_lt_of_lt_ofReal hdist) hC).trans hdeta
  let Z : M × M → E × E := fun pq => e.symm (c pq.1, c pq.2)
  let H : ℝ × (M × M) → M := fun w => curve (Z w.2) w.1

  have hvelocity {gamma : ℝ → M}
      (hgamma : g.IsGeodesicOn gamma (Icc (0 : ℝ) 1))
      {p : M} (hp : p ∈ O) (hstart : gamma 0 = p) :
      ‖deriv (fun t => c (gamma t)) 0‖ ≤
        C * g.tangentNorm (gamma 0)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma 0 1) := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hsrc : gamma 0 ∈ c.source := by simpa only [hstart] using hOsource hp
    have hd := (hgamma.hasDerivAt_chart_at h0 p0 hsrc).1
    have heq : gamma =ᶠ[𝓝 0] fun t => c.symm (c (gamma t)) := by
      filter_upwards [(hgamma.contMDiffAt h0).continuousAt.preimage_mem_nhds
        (hcopen.mem_nhds hsrc)] with t ht
      exact (c.left_inv ht).symm
    have hmetric : g.tangentNorm (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma 0 1) =
        g.tangentNorm (c.symm (c p))
          (mfderiv (𝓡 n) (𝓡 n) c.symm (c p)
            (deriv (fun t => c (gamma t)) 0)) := by
      rw [← hstart]
      conv_lhs => rw [heq.mfderiv_eq, heq.self_of_nhds]
      have hh := g.tangentNorm_chart_curve p0 hd (c.map_source hsrc)
      simpa +instances only [c, RiemannianMetric.tangentNorm,
        RiemannianMetric.pullbackCoefficients, ContinuousLinearMap.bilinearComp_apply] using! hh
    rw [hmetric]
    exact hnorm _ (hOV hp) _

  have hmatch {p q : M} (hp : p ∈ O) (hq : q ∈ O)
      {gamma : ℝ → M} (hgamma : g.IsGeodesicOn gamma (Icc (0 : ℝ) 1))
      (hstart : gamma 0 = p) (hfinish : gamma 1 = q)
      (hspeed : g.tangentNorm (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma 0 1) = (g.edist p q).toReal) :
      ∀ t ∈ Icc (0 : ℝ) 1, gamma =ᶠ[𝓝 t] fun t => H (t, p, q) := by
    let v : E := deriv (fun t => c (gamma t)) 0
    have hv : v ∈ ball (0 : E) eta := by
      have hh := hvelocity hgamma hp hstart
      rw [hspeed] at hh
      simpa only [Metric.mem_ball, dist_zero_right] using hh.trans_lt (hpqSmall hp hq).2
    have hz : (c p, v) ∈ e.source := hbox (hOcoord hp) hv
    have heq0 : gamma 0 = curve (c p, v) 0 := by
      rw [hstart, hcurve0 _ hz, c.left_inv (hOsource hp)]
    have hder0 : deriv (fun t => c (gamma t)) 0 =
        deriv (fun t => c (curve (c p, v) t)) 0 := (hcurveDeriv _ hz).deriv.symm
    have hgeq := hgamma.eq_nhds_on_of_initial_data
        (show g.IsGeodesicOn (curve (c p, v)) (Icc (0 : ℝ) 1) from
          fun t ht => hcurve _ hz t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (convex_Icc (0 : ℝ) 1).isPreconnected (t₀ := 0) (by norm_num) p0
        (by simpa only [hstart] using hOsource hp) heq0 hder0
    have hend : curve (c p, v) 1 = q :=
      (hgeq 1 (by norm_num)).self_of_nhds.symm.trans hfinish
    have hcoordEnd : (e (c p, v)).2 = c q := by
      have hh := congrArg c hend
      rw [hcurve1 _ hz] at hh
      have ht : (e (c p, v)).2 ∈ c.target := by
        rw [← (hspec _ hz).2.1]
        exact ((hspec _ hz).2.2 1 (by norm_num)).1
      rwa [c.right_inv ht] at hh
    have hepair : e (c p, v) = (c p, c q) :=
      Prod.ext (hefirst _ hz) hcoordEnd
    have hinput : Z (p, q) = (c p, v) := by
      change e.symm (c p, c q) = (c p, v)
      rw [← hepair, e.left_inv hz]
    intro t ht
    simpa only [H, hinput] using hgeq t ht
  refine ⟨O, hOopen, hpO, ?_⟩
  intro p hp q hq gamma eta hgamma0' heta0' hgamma0 heta0 hgamma1 heta1 hsGamma hsEta t ht
  exact ((hmatch hp hq hgamma0' hgamma0 hgamma1 hsGamma t ht).self_of_nhds).trans
    ((hmatch hp hq heta0' heta0 heta1 hsEta t ht).self_of_nhds).symm

end PoincareConjecture
