import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Metric.Distortion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Topology.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.LimitTransport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem eventually_source_ball_subset_terminal_image
    (hconv : M23TerminalMetricConvergence G e)
    (hbase : ∀ k, (e k).toFun (0, G.limit.base) =
      (0, (S.term (G.subsequence k)).base))
    {r C : ℝ} (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop,
      ((S.term (G.subsequence k)).flow.flow.metric 0).ball
        (S.term (G.subsequence k)).base r ⊆
      (fun x => ((e k).toFun (0, x)).2) ''
        (G.limit.flow.flow.metric 0).ball G.limit.base (C * r) := by
  let g := G.limit.flow.flow.metric 0
  let R := 2 * C * r
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hR : 0 < R := by dsimp [R]; positivity
  have hcompact := g.isCompact_closure_ball_of_metricComplete
    (G.limit.flow.complete 0 le_rfl) G.limit.base R
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j,
    hconv.eventually_tangentNorm_bounds_on_compact hcompact hC] with k hk hnorm
  let E := (e k).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  let gk := (S.term (G.subsequence k)).flow.flow.metric 0
  have hsource : closure (g.ball G.limit.base R) ⊆ E.source := hj.trans (hmono hk)
  have hE : ContMDiffOn (𝓡 3) (𝓡 3) 1 E E.source :=
    ((e k).spatialHomeomorph_contMDiffOn (mem_Iic.mpr le_rfl)
      (G.exhaustion_open k)).of_le (by simp)
  have hEi : ContMDiffOn (𝓡 3) (𝓡 3) 1 E.symm E.target :=
    ((e k).spatialHomeomorph_symm_contMDiffOn (mem_Iic.mpr le_rfl)
      (G.exhaustion_open k)).of_le (by simp)
  have hEd : E.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨hE.mdifferentiableOn one_ne_zero, hEi.mdifferentiableOn one_ne_zero⟩
  have hinverse := g.inverse_tangentNorm_le_of_le gk E hEd hsource
    (fun x hx v => (hnorm x hx v).2)
  have hcover := g.ball_subset_image_ball_of_inverse_tangentNorm_le gk E G.limit.base
    hR hCpos (show C * r < R by dsimp [R]; nlinarith [mul_pos hCpos hr])
    hcompact hsource (fun x hx => hEi.contMDiffAt (E.open_target.mem_nhds hx)) hinverse
  have hp : E G.limit.base = (S.term (G.subsequence k)).base := congrArg Prod.snd (hbase k)
  rwa [hp] at hcover

theorem eventually_terminal_inverse_edist_bounds
    (hconv : M23TerminalMetricConvergence G e)
    (hbase : ∀ k, (e k).toFun (0, G.limit.base) =
      (0, (S.term (G.subsequence k)).base))
    {A C : ℝ} (hA : 0 < A) (hC : 1 < C) :
    ∀ᶠ k in atTop, ∀ x ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
        (S.term (G.subsequence k)).base A,
      ∀ y ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
        (S.term (G.subsequence k)).base A,
      let inv := fun z => ((e k).inverse (0, z)).2
      (G.limit.flow.flow.metric 0).edist (inv x) (inv y) ≤
          ENNReal.ofReal C * ((S.term (G.subsequence k)).flow.flow.metric 0).edist x y ∧
        ((S.term (G.subsequence k)).flow.flow.metric 0).edist x y ≤
          ENNReal.ofReal C * (G.limit.flow.flow.metric 0).edist (inv x) (inv y) := by
  let g := G.limit.flow.flow.metric 0
  let K := closure (g.ball G.limit.base (6 * A))
  have hK := g.isCompact_closure_ball_of_metricComplete
    (G.limit.flow.complete 0 le_rfl) G.limit.base (6 * A)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j,
    hconv.eventually_source_ball_subset_terminal_image hbase hA (by norm_num : (1 : ℝ) < 2),
    hconv.eventually_source_ball_subset_terminal_image hbase
      (show 0 < 3 * A by positivity) (by norm_num : (1 : ℝ) < 2),
    hconv.eventually_tangentNorm_bounds_on_compact hK hC] with k hk hcover hcover3 hnorm
  let E := (e k).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  let gk := (S.term (G.subsequence k)).flow.flow.metric 0
  let p := (S.term (G.subsequence k)).base
  have hsource : K ⊆ E.source := hj.trans (hmono hk)
  have hE : ContMDiffOn (𝓡 3) (𝓡 3) 1 E E.source :=
    ((e k).spatialHomeomorph_contMDiffOn (mem_Iic.mpr le_rfl)
      (G.exhaustion_open k)).of_le (by simp)
  have hEi : ContMDiffOn (𝓡 3) (𝓡 3) 1 E.symm E.target :=
    ((e k).spatialHomeomorph_symm_contMDiffOn (mem_Iic.mpr le_rfl)
      (G.exhaustion_open k)).of_le (by simp)
  have hEd : E.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨hE.mdifferentiableOn one_ne_zero, hEi.mdifferentiableOn one_ne_zero⟩
  have hinverse := g.inverse_tangentNorm_le_of_le gk E hEd hsource
    (fun z hz v => (hnorm z hz v).2)
  have hcoverK : gk.ball p (3 * A) ⊆ E '' K := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hcover3 hz
    exact ⟨w, subset_closure (by simpa only [show 2 * (3 * A) = 6 * A by ring] using hw), rfl⟩
  have htarget : gk.ball p (3 * A) ⊆ E.target :=
    hcoverK.trans (E.mapsTo.mono_left hsource).image_subset
  have hback {x y} (hx : x ∈ gk.ball p A) (hy : y ∈ gk.ball p A) :
      g.edist (E.symm x) (E.symm y) ≤ ENNReal.ofReal C * gk.edist x y :=
    gk.edist_image_le_mul_edist_of_tangentNorm_le_on_ball g E.symm p hA
      (zero_lt_one.trans hC)
      (fun z hz => hEi.contMDiffAt (E.open_target.mem_nhds (htarget hz)))
      (fun z hz v => hinverse z (hcoverK hz) v) hx hy
  have hpre {x} (hx : x ∈ gk.ball p A) :
      E.symm x ∈ g.ball G.limit.base (2 * A) ∧ E (E.symm x) = x := by
    obtain ⟨z, hz, rfl⟩ := hcover hx
    have hzK : z ∈ K := subset_closure
      (hz.trans_le (ENNReal.ofReal_le_ofReal (by linarith : 2 * A ≤ 6 * A)))
    change E.symm (E z) ∈ g.ball G.limit.base (2 * A) ∧ E (E.symm (E z)) = E z
    rw [E.left_inv (hsource hzK)]
    exact ⟨hz, rfl⟩
  intro x hx y hy
  obtain ⟨hxL, hxE⟩ := hpre hx
  obtain ⟨hyL, hyE⟩ := hpre hy
  refine ⟨hback hx hy, ?_⟩
  have hforward := g.edist_image_le_mul_edist_of_tangentNorm_le_on_ball gk E
    G.limit.base (show 0 < 2 * A by positivity) (zero_lt_one.trans hC)
    (fun z hz => hE.contMDiffAt (E.open_source.mem_nhds (hsource (subset_closure (by
      simpa only [show 3 * (2 * A) = 6 * A by ring] using hz)))))
    (fun z hz v => (hnorm z (subset_closure (by
      simpa only [show 3 * (2 * A) = 6 * A by ring] using hz)) v).1) hxL hyL
  rwa [hxE, hyE] at hforward

theorem eventually_terminal_inverse_distance_error
    (hconv : M23TerminalMetricConvergence G e)
    (hbase : ∀ k, (e k).toFun (0, G.limit.base) =
      (0, (S.term (G.subsequence k)).base))
    {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
        (S.term (G.subsequence k)).base A,
      ∀ y ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
        (S.term (G.subsequence k)).base A,
      let inv := fun z => ((e k).inverse (0, z)).2
      |((G.limit.flow.flow.metric 0).edist (inv x) (inv y)).toReal -
        (((S.term (G.subsequence k)).flow.flow.metric 0).edist x y).toReal| < ε := by
  let C := 1 + ε / (4 * A)
  have hC : 1 < C := by
    have h : 0 < ε / (4 * A) := by positivity
    dsimp [C]
    linarith
  have herror : (C - 1) * (2 * A) < ε := by
    dsimp [C]
    field_simp
    nlinarith
  filter_upwards [hconv.eventually_terminal_inverse_edist_bounds hbase hA hC] with k hk
  intro x hx y hy
  let g := G.limit.flow.flow.metric 0
  let gk := (S.term (G.subsequence k)).flow.flow.metric 0
  let p := (S.term (G.subsequence k)).base
  let inv := fun z => ((e k).inverse (0, z)).2
  have hh := hk x hx y hy
  have hLS := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (gk.edist_ne_top x y)) hh.1
  have hSL := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (g.edist_ne_top (inv x) (inv y))) hh.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (zero_le_one.trans hC.le)] at hLS hSL
  have hsource : (gk.edist x y).toReal < 2 * A := by
    let : MetricSpace (S.term (G.subsequence k)).carrier.carrier :=
      (S.term (G.subsequence k)).carrier.metricSpaceOf gk
    have hx' : dist p x < A := (ENNReal.lt_ofReal_iff_toReal_lt (gk.edist_ne_top _ _)).mp hx
    have hy' : dist p y < A := (ENNReal.lt_ofReal_iff_toReal_lt (gk.edist_ne_top _ _)).mp hy
    have ht := dist_triangle x p y
    rw [dist_comm x p] at ht
    change dist x y < 2 * A
    linarith
  change |(g.edist (inv x) (inv y)).toReal - (gk.edist x y).toReal| < ε
  have hprod := mul_le_mul_of_nonneg_left hsource.le (sub_pos.mpr hC).le
  apply abs_lt.mpr
  constructor
  · by_cases hab : (g.edist (inv x) (inv y)).toReal ≤ (gk.edist x y).toReal
    · have ha := mul_le_mul_of_nonneg_left hab (sub_pos.mpr hC).le
      nlinarith
    · linarith
  · nlinarith

theorem tendsto_terminal_inverse_distance
    (hconv : M23TerminalMetricConvergence G e)
    (hbase : ∀ k, (e k).toFun (0, G.limit.base) =
      (0, (S.term (G.subsequence k)).base))
    (x y : ∀ k, (S.term (G.subsequence k)).carrier.carrier)
    {A D : ℝ} (hA : 0 < A)
    (hx : ∀ᶠ k in atTop, x k ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
      (S.term (G.subsequence k)).base A)
    (hy : ∀ᶠ k in atTop, y k ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
      (S.term (G.subsequence k)).base A)
    (hd : Tendsto (fun k =>
      (((S.term (G.subsequence k)).flow.flow.metric 0).edist (x k) (y k)).toReal)
      atTop (𝓝 D)) :
    Tendsto (fun k => ((G.limit.flow.flow.metric 0).edist
      ((e k).inverse (0, x k)).2 ((e k).inverse (0, y k)).2).toReal) atTop (𝓝 D) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hx, hy, (Metric.tendsto_nhds.mp hd) (ε / 2) (by positivity),
    hconv.eventually_terminal_inverse_distance_error hbase hA
      (show 0 < ε / 2 by positivity)] with k hkx hky hkd hki
  have herr := hki (x k) hkx (y k) hky
  rw [Real.dist_eq] at hkd ⊢
  have htriangle := abs_sub_le
    (((G.limit.flow.flow.metric 0).edist
      ((e k).inverse (0, x k)).2 ((e k).inverse (0, y k)).2).toReal)
    ((((S.term (G.subsequence k)).flow.flow.metric 0).edist (x k) (y k)).toReal) D
  linarith

end M23TerminalMetricConvergence

end PoincareConjecture
