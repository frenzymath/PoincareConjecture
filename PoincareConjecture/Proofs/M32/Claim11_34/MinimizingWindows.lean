import PoincareConjecture.Proofs.M32.Claim11_34.ForwardComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.IntrinsicMinimizer
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.ProjIcc
















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space




theorem blowup_eventually_minimizing_window_of_annulus_separation
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J)
    (Sigma : ∀ n, Set ((S.flow n).slice (S.base n).1).carrier)
    {D R : ℝ} (hD : 0 < D)
    (hSigma : ∀ᶠ n in atTop, Sigma n ⊆ S.baseBall n D)
    (hR : 2 * (2 * D + 1 + 1) < R)
    (hannulus : ∀ᶠ n in atTop, ∃ yNeg yPos,
      yNeg ∈ S.baseBall n (2 * R) \ S.baseBall n R ∧
      yPos ∈ S.baseBall n (2 * R) \ S.baseBall n R ∧
      ¬ JoinedIn (Sigma n)ᶜ yNeg yPos) :
    ∀ᶠ k in atTop, ∃ a b : ℝ, ∃ arc : ℝ → G.limit.carrier.carrier,
      R / 2 - (2 * D + 1) ≤ a ∧ R / 2 - (2 * D + 1) ≤ b ∧
      Continuous arc ∧
      (∀ t, arc t ∈ (blowup_zeroSliceEmbedding G k).source) ∧
      arc 0 ∈ (G.limit.flow.metric 0).ball G.limit.base (2 * D) ∧
      blowup_zeroSliceEmbedding G k (arc 0) ∈ Sigma (G.subsequence k) ∧
      (∀ s ∈ Icc (-a) b, ∀ t ∈ Icc (-a) b,
        (G.limit.flow.metric 0).edist (arc s) (arc t) = ENNReal.ofReal |s - t|) ∧
      blowup_zeroSliceEmbedding G k (arc (-a)) ∈
        S.baseBall (G.subsequence k) (2 * R) \ S.baseBall (G.subsequence k) R ∧
      blowup_zeroSliceEmbedding G k (arc b) ∈
        S.baseBall (G.subsequence k) (2 * R) \ S.baseBall (G.subsequence k) R ∧
      ¬ JoinedIn (Sigma (G.subsequence k))ᶜ
        (blowup_zeroSliceEmbedding G k (arc (-a)))
        (blowup_zeroSliceEmbedding G k (arc b)) ∧
      (∀ x ∈ (blowup_zeroSliceEmbedding G k).source,
        blowup_zeroSliceEmbedding G k x ∈ Sigma (G.subsequence k) →
        x ∈ (G.limit.flow.metric 0).ball G.limit.base (2 * D)) := by
  classical
  let g := G.limit.flow.metric 0
  let p := G.limit.base
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  let : ProperSpace G.limit.carrier.carrier :=
    g.properSpace_toMetricSpace (G.limit.complete 0 G.limit.zero_mem)
  have hRpos : 0 < R := by linarith
  have hDR : D < R := by linarith
  let K := Metric.closedBall p (12 * R + 1)
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G (isCompact_closedBall p (12 * R + 1))
  have hSigma' := G.subsequence_strictMono.tendsto_atTop.eventually hSigma
  have hannulus' := G.subsequence_strictMono.tendsto_atTop.eventually hannulus
  filter_upwards [hSigma', hannulus',
    blowup_eventually_zeroSliceEmbedding_inverse_ball G (show 0 < 2 * R by positivity)
      (show (1 : ℝ) < 2 by norm_num),
    blowup_eventually_zeroSliceEmbedding_inverse_ball G hD (show (1 : ℝ) < 2 by norm_num),
    blowup_eventually_zeroSliceEmbedding_image_ball G (show 0 < R / 2 by positivity)
      (show (1 : ℝ) < 2 by norm_num), eventually_ge_atTop j]
    with k hSk hAk hinverse hsmall hforward hjk
  let e : OpenPartialHomeomorph G.limit.carrier.carrier
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier :=
    blowup_zeroSliceEmbedding G k
  have hsource : K ⊆ e.source := by
    intro x hx
    change x ∈ (blowup_zeroSliceEmbedding G k).source
    rw [blowup_zeroSliceEmbedding_source]
    exact G.exhaustion.space_increasing hjk (hj hx)
  have hpreimage (x : G.limit.carrier.carrier) (hx : x ∈ e.source)
      (hxS : e x ∈ Sigma (G.subsequence k)) : x ∈ g.ball p (2 * D) := by
    have h := (hsmall (e x) (hSk hxS)).2
    change e.symm (e x) ∈ g.ball p (2 * D) at h
    rwa [e.left_inv hx] at h
  obtain ⟨yNeg, yPos, hyNeg, hyPos, hnot⟩ := hAk
  let xNeg := e.symm yNeg
  let xPos := e.symm yPos
  have hn := hinverse yNeg hyNeg.1
  have hp := hinverse yPos hyPos.1
  have hxNeg : e xNeg = yNeg := e.right_inv hn.1
  have hxPos : e xPos = yPos := e.right_inv hp.1
  have hupperNeg : dist xNeg p < 4 * R := by
    have h := hn.2
    change xNeg ∈ g.ball p (2 * (2 * R)) at h
    rw [← g.toMetricSpace_ball] at h
    change dist xNeg p < 2 * (2 * R) at h
    linarith
  have hupperPos : dist xPos p < 4 * R := by
    have h := hp.2
    change xPos ∈ g.ball p (2 * (2 * R)) at h
    rw [← g.toMetricSpace_ball] at h
    change dist xPos p < 2 * (2 * R) at h
    linarith
  have hlower (y : ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier)
      (hy : y ∉ S.baseBall (G.subsequence k) R) (hyt : y ∈ e.target) :
      R / 2 ≤ dist (e.symm y) p := by
    by_contra h
    have hball : e.symm y ∈ g.ball p (R / 2) := by
      rw [← g.toMetricSpace_ball]
      exact lt_of_not_ge h
    have him := hforward.2 (mem_image_of_mem e hball)
    rw [e.right_inv hyt] at him
    have hrad : (2 : ℝ) * (R / 2) = R := by ring
    rw [hrad] at him
    exact hy him
  have hlowerNeg := hlower yNeg hyNeg.2 hn.1
  have hlowerPos := hlower yPos hyPos.2 hp.1
  have hyNegS : yNeg ∉ Sigma (G.subsequence k) := by
    intro h
    apply hyNeg.2
    have hy := hSk h
    exact hy.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hDR.le (Real.sqrt_nonneg _)))
  have hne : xNeg ≠ xPos := by
    intro h
    have heq : yNeg = yPos := hxNeg.symm.trans ((congrArg e h).trans hxPos)
    apply hnot
    rw [← heq]
    exact JoinedIn.refl hyNegS
  let L := dist xNeg xPos
  have hL : 0 < L := dist_pos.mpr hne
  have hLupper : L < 8 * R := by
    have h := dist_triangle xNeg p xPos
    rw [dist_comm p xPos] at h
    change dist xNeg xPos < 8 * R
    linarith
  have hcompact : IsCompact (closure (g.ball xNeg (L + 1))) := by
    rw [← g.toMetricSpace_ball]
    exact (isCompact_closedBall xNeg (L + 1)).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  have hxPosball : xPos ∈ g.ball xNeg (L + 1) := by
    rw [← g.toMetricSpace_ball]
    change dist xPos xNeg < L + 1
    rw [dist_comm]
    dsimp [L]
    linarith
  obtain ⟨eta, heta0, heta1, _, hetad⟩ :=
    g.exists_intrinsic_metric_segment_of_precompact_ball xNeg xPos
      (show 0 < L + 1 by linarith) hcompact hxPosball
  have hdist (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (eta s) (eta t) = |s - t| * L := by
    have h := hetad s hs t ht
    change edist (eta s) (eta t) = ENNReal.ofReal |s - t| * edist xNeg xPos at h
    have h' := congrArg ENNReal.toReal h
    simpa only [edist_dist, ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h'
  have hetac : ContinuousOn eta (Icc (0 : ℝ) 1) := by
    apply (show LipschitzOnWith (⟨L, hL.le⟩ : NNReal) eta (Icc (0 : ℝ) 1) from ?_).continuousOn
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [hdist s hs t ht, Real.dist_eq]
    exact (mul_comm _ _).le
  have hetaNeg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (eta t) xNeg = t * L := by
    simpa only [heta0, sub_zero, abs_of_nonneg ht.1] using hdist t ht 0 (by norm_num)
  have hetasource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : eta t ∈ e.source := by
    apply hsource
    change dist (eta t) p ≤ 12 * R + 1
    have htri := dist_triangle (eta t) xNeg p
    rw [hetaNeg t ht] at htri
    nlinarith [ht.2]
  obtain ⟨tau, htau, htauS⟩ : ∃ tau ∈ Icc (0 : ℝ) 1,
      e (eta tau) ∈ Sigma (G.subsequence k) := by
    by_contra h
    push Not at h
    apply hnot
    apply JoinedIn.ofLine (e.continuousOn.comp hetac hetasource)
      (by simpa only [Function.comp_apply, heta0] using hxNeg)
      (by simpa only [Function.comp_apply, heta1] using hxPos)
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  have hcenter := hpreimage (eta tau) (hetasource tau htau) htauS
  have hcenterd : dist (eta tau) p < 2 * D := by
    rwa [← g.toMetricSpace_ball] at hcenter
  let a := tau * L
  let b := (1 - tau) * L
  have ha : R / 2 - (2 * D + 1) ≤ a := by
    have htri := dist_triangle xNeg (eta tau) p
    rw [dist_comm xNeg (eta tau), hetaNeg tau htau] at htri
    dsimp [a]
    linarith
  have hb : R / 2 - (2 * D + 1) ≤ b := by
    have hd := hdist tau htau 1 (by norm_num)
    rw [heta1, abs_of_nonpos (sub_nonpos.mpr htau.2), neg_sub] at hd
    have htri := dist_triangle xPos (eta tau) p
    rw [dist_comm xPos (eta tau), hd] at htri
    dsimp [b]
    linarith
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  let parameter (t : ℝ) := projIcc (0 : ℝ) 1 zero_le_one (tau + t / L)
  let arc (t : ℝ) := eta (parameter t)
  have hparameter (t : ℝ) (ht : t ∈ Icc (-a) b) : tau + t / L ∈ Icc (0 : ℝ) 1 := by
    have hlo : -tau ≤ t / L := (le_div_iff₀ hL).mpr (by dsimp [a] at ht; linarith [ht.1])
    have hhi : t / L ≤ 1 - tau := (div_le_iff₀ hL).mpr (by dsimp [b] at ht; linarith [ht.2])
    constructor <;> linarith
  have harc (t : ℝ) (ht : t ∈ Icc (-a) b) : arc t = eta (tau + t / L) := by
    dsimp [arc, parameter]
    rw [projIcc_of_mem zero_le_one (hparameter t ht)]
  have harc0 : arc 0 = eta tau := by
    dsimp [arc, parameter]
    simp only [zero_div, add_zero, projIcc_of_mem zero_le_one htau]
  have harcleft : arc (-a) = xNeg := by
    rw [harc (-a) ⟨le_rfl, by linarith⟩]
    have harg : tau + -a / L = 0 := by dsimp [a]; field_simp [hL.ne']; ring
    rw [harg, heta0]
  have harcright : arc b = xPos := by
    rw [harc b ⟨by linarith, le_rfl⟩]
    have harg : tau + b / L = 1 := by dsimp [b]; field_simp [hL.ne']; ring
    rw [harg, heta1]
  refine ⟨a, b, arc, ha, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpreimage⟩
  · exact hetac.domRestrict.comp (continuous_projIcc.comp
      (continuous_const.add (continuous_id.div_const L)))
  · intro t
    exact hetasource (parameter t) (parameter t).property
  · rw [harc0]
    exact hcenter
  · rw [harc0]
    exact htauS
  · intro s hs t ht
    change edist (arc s) (arc t) = _
    rw [edist_dist, harc s hs, harc t ht, hdist _ (hparameter s hs) _ (hparameter t ht)]
    congr 1
    have harg : tau + s / L - (tau + t / L) = (s - t) / L := by ring
    rw [harg, abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne']
  · change e (arc (-a)) ∈ _
    rw [harcleft, hxNeg]
    exact hyNeg
  · change e (arc b) ∈ _
    rw [harcright, hxPos]
    exact hyPos
  · change ¬ JoinedIn (Sigma (G.subsequence k))ᶜ (e (arc (-a))) (e (arc b))
    rw [harcleft, harcright, hxNeg, hxPos]
    exact hnot

end PoincareConjecture.M32
