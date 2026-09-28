import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.JointCoordinateExponentialInverse
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.FrozenMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

universe u

namespace PoincareConjecture.M63




theorem exists_local_smooth_minimizing_interpolator
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (hcompact : IsCompact (univ : Set M)) (p0 : M) :
    ∃ O : Set M, IsOpen O ∧ p0 ∈ O ∧
      ∃ H : ℝ × (M × M) → M,
        ContMDiffOn
          ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
          (Ioo (-1 : ℝ) 2 ×ˢ (O ×ˢ O)) ∧
        (∀ p ∈ O, ∀ q ∈ O,
          g.edist p q < ENNReal.ofReal 1 ∧
          H (0, p, q) = p ∧ H (1, p, q) = q ∧
          g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
          (∀ t ∈ Ioo (-1 : ℝ) 2,
            g.tangentNorm (H (t, p, q))
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, p, q)) t 1) =
                (g.edist p q).toReal) ∧
          g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q ∧
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            g.edist (H (s, p, q)) (H (t, p, q)) =
              ENNReal.ofReal |s - t| * g.edist p q)) ∧
        (∀ p ∈ O, ∀ t ∈ Ioo (-1 : ℝ) 2, H (t, p, p) = p) ∧
        (∀ p ∈ O, ∀ q ∈ O, ∀ gamma : ℝ → M,
          g.IsGeodesicOn gamma (Ioo (-1 : ℝ) 2) →
          gamma 0 = p → gamma 1 = q →
          g.pathELength gamma 0 1 = g.edist p q →
          EqOn gamma (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2)) := by
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
  have hZ {p q : M} (hp : p ∈ O) (hq : q ∈ O) : Z (p, q) ∈ e.source :=
    e.map_target (hpqTarget hp hq)
  have hZfirst {p q : M} (hp : p ∈ O) (hq : q ∈ O) : (Z (p, q)).1 = c p := by
    exact (hefirst _ (hZ hp hq)).symm.trans
      (congrArg Prod.fst (e.right_inv (hpqTarget hp hq)))
  have hH0 {p q : M} (hp : p ∈ O) (hq : q ∈ O) : H (0, p, q) = p := by
    change curve (Z (p, q)) 0 = p
    rw [hcurve0 _ (hZ hp hq), hZfirst hp hq]
    exact c.left_inv (hOsource hp)
  have hH1 {p q : M} (hp : p ∈ O) (hq : q ∈ O) : H (1, p, q) = q := by
    change curve (Z (p, q)) 1 = q
    rw [hcurve1 _ (hZ hp hq), e.right_inv (hpqTarget hp hq)]
    exact c.left_inv (hOsource hq)
  have hHgeo {p q : M} (hp : p ∈ O) (hq : q ∈ O) :
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) := by
    intro t ht
    exact hcurve _ (hZ hp hq) t ⟨by linarith [ht.1], ht.2⟩
  have hHsmooth : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ (O ×ˢ O)) := by
    have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := by
      simpa only [c, extChartAt_source] using
        (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := p0))
    have hcoords : ContMDiffOn ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, E × E) ∞
        (fun pq : M × M => (c pq.1, c pq.2)) (O ×ˢ O) :=
      (hc.comp contMDiff_fst.contMDiffOn (fun _ hw => hOsource hw.1)).prodMk_space
        (hc.comp contMDiff_snd.contMDiffOn (fun _ hw => hOsource hw.2))
    have hZm : ContMDiffOn ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, E × E) ∞ Z (O ×ˢ O) :=
      (contMDiffOn_iff_contDiffOn.mpr hei).comp hcoords
        (fun _ hw => hpqTarget hw.1 hw.2)
    have hinput : ContMDiffOn
        ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) 𝓘(ℝ, (E × E) × ℝ) ∞
        (fun w : ℝ × (M × M) => (Z w.2, w.1))
        (Ioo (-1 : ℝ) 2 ×ˢ (O ×ˢ O)) :=
      (hZm.comp contMDiff_snd.contMDiffOn (fun _ hw => hw.2)).prodMk_space
        contMDiff_fst.contMDiffOn
    have hpos : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓡 n) ∞
        (fun w => (Gamma w).1) (e.source ×ˢ Ioo (-2 : ℝ) 2) :=
      contMDiffOn_iff_contDiffOn.mpr hGamma.fst
    exact (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p0).comp
      (hpos.comp hinput (fun _ hw =>
        ⟨hZ hw.2.1 hw.2.2, by constructor <;> linarith [hw.1.1, hw.1.2]⟩))
      (fun w hw => ((hspec _ (hZ hw.2.1 hw.2.2)).2.2 w.1
        ⟨by linarith [hw.1.1], hw.1.2⟩).1)
  have hclosed {eps : ℝ} (heps : 0 < eps) :
      Icc (0 : ℝ) 1 ⊆ Ioo (-eps) (1 + eps) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]

  have hvelocity {eps : ℝ} (heps : 0 < eps) {gamma : ℝ → M}
      (hgamma : g.IsGeodesicOn gamma (Ioo (-eps) (1 + eps)))
      {p : M} (hp : p ∈ O) (hstart : gamma 0 = p) :
      ‖deriv (fun t => c (gamma t)) 0‖ ≤
        C * g.tangentNorm (gamma 0)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma 0 1) := by
    have h0 : (0 : ℝ) ∈ Ioo (-eps) (1 + eps) := hclosed heps (by norm_num)
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
  have hspeedOfLength {eps : ℝ} (heps : 0 < eps) {gamma : ℝ → M}
      (hgamma : g.IsGeodesicOn gamma (Ioo (-eps) (1 + eps)))
      {p q : M} (hlength : g.pathELength gamma 0 1 = g.edist p q) :
      ∀ t ∈ Ioo (-eps) (1 + eps),
        g.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1) =
          (g.edist p q).toReal := by
    obtain ⟨Cs, hCs⟩ := hgamma.exists_constant_tangentNorm (by linarith)
    have hlengthCs : g.pathELength gamma 0 1 = ENNReal.ofReal (Cs : ℝ) := by
      simpa using g.pathELength_eq_of_tangentNorm_eq (a := 0) (b := 1)
        (fun t ht => hCs t (hclosed heps ht))
    have hCsD : (Cs : ℝ) = (g.edist p q).toReal := by
      have hh := congrArg ENNReal.toReal (hlengthCs.symm.trans hlength)
      exact (ENNReal.toReal_ofReal Cs.2).symm.trans hh
    exact fun t ht => (hCs t ht).trans hCsD

  have hmatch {p q : M} (hp : p ∈ O) (hq : q ∈ O)
      {eps : ℝ} (heps : 0 < eps) {gamma : ℝ → M}
      (hgamma : g.IsGeodesicOn gamma (Ioo (-eps) (1 + eps)))
      (hstart : gamma 0 = p) (hfinish : gamma 1 = q)
      (hspeed : g.tangentNorm (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma 0 1) = (g.edist p q).toReal) :
      ∀ t ∈ Icc (0 : ℝ) 1, gamma =ᶠ[𝓝 t] fun t => H (t, p, q) := by
    let v : E := deriv (fun t => c (gamma t)) 0
    have hv : v ∈ ball (0 : E) eta := by
      have hh := hvelocity heps hgamma hp hstart
      rw [hspeed] at hh
      simpa only [Metric.mem_ball, dist_zero_right] using hh.trans_lt (hpqSmall hp hq).2
    have hz : (c p, v) ∈ e.source := hbox (hOcoord hp) hv
    have heq0 : gamma 0 = curve (c p, v) 0 := by
      rw [hstart, hcurve0 _ hz, c.left_inv (hOsource hp)]
    have hder0 : deriv (fun t => c (gamma t)) 0 =
        deriv (fun t => c (curve (c p, v) t)) 0 := (hcurveDeriv _ hz).deriv.symm
    have hgeq := (show g.IsGeodesicOn gamma (Icc (0 : ℝ) 1) from
      fun t ht => hgamma t (hclosed heps ht)).eq_nhds_on_of_initial_data
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
  have hproperties (p : M) (hp : p ∈ O) (q : M) (hq : q ∈ O) :
      g.edist p q < ENNReal.ofReal 1 ∧
      H (0, p, q) = p ∧ H (1, p, q) = q ∧
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal) ∧
      g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (H (s, p, q)) (H (t, p, q)) =
          ENNReal.ofReal |s - t| * g.edist p q) := by
    obtain ⟨eps, heps, gamma, hgamma, hstart, hfinish, hmin⟩ :=
      g.exists_minimizing_geodesic_of_precompact_ball p q (by norm_num : (0 : ℝ) < 1)
        (hcompact.of_isClosed_subset isClosed_closure (subset_univ _)) (hpqSmall hp hq).1
    have hlength := hgamma.pathELength_eq_of_edist_segment heps hstart hmin
    have hspeed := hspeedOfLength heps hgamma hlength
    have hgeq := hmatch hp hq heps hgamma hstart hfinish
      (hspeed 0 (hclosed heps (by norm_num)))
    have hH0speed : g.tangentNorm (H (0, p, q))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun t => H (t, p, q)) 0 1) =
          (g.edist p q).toReal := by
      have hh := hspeed 0 (hclosed heps (by norm_num))
      rw [(hgeq 0 (by norm_num)).mfderiv_eq,
        (hgeq 0 (by norm_num)).self_of_nhds] at hh
      exact hh
    obtain ⟨Cs, hCs⟩ := (hHgeo hp hq).exists_constant_tangentNorm (by norm_num)
    have hCsD : (Cs : ℝ) = (g.edist p q).toReal :=
      (hCs 0 (by norm_num)).symm.trans hH0speed
    have hHspeed : ∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal := fun t ht => (hCs t ht).trans hCsD
    have hfinite : g.edist p q ≠ ⊤ := ne_top_of_lt ((hpqSmall hp hq).1.trans_le le_top)
    refine ⟨(hpqSmall hp hq).1, hH0 hp hq, hH1 hp hq, hHgeo hp hq, hHspeed, ?_, ?_⟩
    · have hh := g.pathELength_eq_of_tangentNorm_eq (a := 0) (b := 1)
        (fun t ht => hHspeed t (by constructor <;> linarith [ht.1, ht.2]))
      simpa only [sub_zero, ENNReal.ofReal_one, mul_one,
        ENNReal.ofReal_toReal hfinite] using hh
    · intro s hs t ht
      have hgs : gamma s = H (s, p, q) := (hgeq s hs).self_of_nhds
      have hgt : gamma t = H (t, p, q) := (hgeq t ht).self_of_nhds
      rw [← hgs, ← hgt]
      exact hmin s hs t ht
  have hunique (p : M) (hp : p ∈ O) (q : M) (hq : q ∈ O) (gamma : ℝ → M)
      (hgamma : g.IsGeodesicOn gamma (Ioo (-1 : ℝ) 2))
      (hstart : gamma 0 = p) (hfinish : gamma 1 = q)
      (hlength : g.pathELength gamma 0 1 = g.edist p q) :
      EqOn gamma (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) := by
    have hgamma' : g.IsGeodesicOn gamma (Ioo (-1 : ℝ) (1 + 1)) := by
      simpa only [one_add_one_eq_two] using hgamma
    have hspeed := hspeedOfLength zero_lt_one hgamma' hlength
    exact hgamma.eqOn_of_eq_nhds (hHgeo hp hq) (convex_Ioo (-1 : ℝ) 2).isPreconnected
      (t₀ := 0) (by norm_num)
      (hmatch hp hq zero_lt_one hgamma' hstart hfinish
        (hspeed 0 (by norm_num)) 0 (by norm_num))
  refine ⟨O, hOopen, hpO, H, hHsmooth, hproperties, ?_, hunique⟩
  intro p hp t ht
  have hconst : g.pathELength (fun _ : ℝ => p) 0 1 = g.edist p p := by
    have hz : ∀ s ∈ Icc (0 : ℝ) 1,
        g.tangentNorm p (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun _ : ℝ => p) s 1) = 0 := by
      intro s _
      simp [RiemannianMetric.tangentNorm]
    simpa only [ENNReal.ofReal_zero, zero_mul, RiemannianMetric.edist,
      Manifold.riemannianEDist_self] using g.pathELength_eq_of_tangentNorm_eq hz
  exact (hunique p hp p hp (fun _ => p) (g.isGeodesicOn_const p _)
    rfl rfl hconst ht).symm

end PoincareConjecture.M63
