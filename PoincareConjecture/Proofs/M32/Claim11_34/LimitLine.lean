import PoincareConjecture.Proofs.M32.Claim11_34.MinimizingWindows
import PoincareConjecture.Proofs.M32.Mathlib.BoundedAnchorLine
import Mathlib.Topology.Connected.LocallyPathConnected

















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

private theorem joinedIn_of_continuousOn_interval
    {X : Type*} [TopologicalSpace X] {f : ℝ → X} {a b : ℝ} {U : Set X}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hmap : MapsTo f (Icc a b) U) :
    JoinedIn U (f a) (f b) := by
  have hparam : MapsTo (fun t : ℝ => a + (b - a) * t) (Icc (0 : ℝ) 1) (Icc a b) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  apply JoinedIn.ofLine
    (hf.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn hparam)
    (by simp) (by simp)
  rintro _ ⟨t, ht, rfl⟩
  exact hmap (hparam ht)

private theorem exists_precompact_pathConnected_nhds_outside_closedBall
    {X : Type*} [MetricSpace X] [ProperSpace X] [LocallyPathConnectedSpace X]
    {p x : X} {B : ℝ} (hx : B < dist x p) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsPathConnected V ∧
      IsCompact (closure V) ∧ closure V ⊆ (Metric.closedBall p B)ᶜ := by
  let r := (dist x p - B) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let V := pathComponentIn (Metric.ball x r) x
  have hxball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hclosure : closure V ⊆ Metric.closedBall x r :=
    closure_minimal (pathComponentIn_subset.trans Metric.ball_subset_closedBall)
      Metric.isClosed_closedBall
  refine ⟨V, Metric.isOpen_ball.pathComponentIn x, mem_pathComponentIn_self hxball,
    isPathConnected_pathComponentIn hxball,
    (isCompact_closedBall x r).of_isClosed_subset isClosed_closure hclosure, ?_⟩
  intro y hy hK
  have hnear : dist y x ≤ r := hclosure hy
  have hinside : dist y p ≤ B := hK
  have htri := dist_triangle x y p
  rw [dist_comm x y] at htri
  dsimp [r] at hnear
  linarith

private theorem window_truncation_not_joined
    {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {Sigma : Set Y} {p : X}
    {a b B T : ℝ} {arc : ℝ → X}
    (hc : Continuous arc) (hsource : ∀ t, arc t ∈ e.source)
    (hdist : ∀ s ∈ Icc (-a) b, ∀ t ∈ Icc (-a) b,
      dist (arc s) (arc t) = |s - t|)
    (hanchor : dist (arc 0) p ≤ B)
    (hpreimage : ∀ x ∈ e.source, e x ∈ Sigma → dist x p ≤ B)
    (hnot : ¬ JoinedIn Sigmaᶜ (e (arc (-a))) (e (arc b)))
    (hB : 0 ≤ B) (hT : 2 * B + 1 < T) (ha : T ≤ a) (hb : T ≤ b) :
    ¬ JoinedIn Sigmaᶜ (e (arc (-T))) (e (arc T)) := by
  have hTpos : 0 < T := by linarith
  have hzero : (0 : ℝ) ∈ Icc (-a) b := ⟨by linarith, by linarith⟩
  have hcontinuous : Continuous (fun t => e (arc t)) :=
    e.continuousOn.comp_continuous hc hsource
  have havoid (t : ℝ) (ht : t ∈ Icc (-a) b) (htail : T ≤ |t|) :
      e (arc t) ∉ Sigma := by
    intro h
    have hd := hdist t ht 0 hzero
    rw [sub_zero] at hd
    have htri := dist_triangle (arc t) p (arc 0)
    rw [dist_comm p (arc 0), hd] at htri
    have hbound := hpreimage (arc t) (hsource t) h
    linarith
  have hleft : JoinedIn Sigmaᶜ (e (arc (-a))) (e (arc (-T))) := by
    apply joinedIn_of_continuousOn_interval (by linarith) hcontinuous.continuousOn
    intro t ht
    apply havoid t ⟨ht.1, by linarith [ht.2]⟩
    rw [abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.2]
  have hright : JoinedIn Sigmaᶜ (e (arc T)) (e (arc b)) := by
    apply joinedIn_of_continuousOn_interval hb hcontinuous.continuousOn
    intro t ht
    apply havoid t ⟨by linarith [ht.1], ht.2⟩
    rw [abs_of_nonneg (by linarith [ht.1])]
    exact ht.1
  exact fun h => hnot ((hleft.trans h).trans hright)

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space





theorem blowup_exists_minimizing_line_and_compact_separator
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J)
    (Sigma : ∀ n, Set ((S.flow n).slice (S.base n).1).carrier)
    {D R₀ : ℝ} (hD : 0 < D)
    (hSigma : ∀ᶠ n in atTop, Sigma n ⊆ S.baseBall n D) (hR₀ : 0 ≤ R₀)
    (hannulus : ∀ R : ℝ, R₀ < R → ∀ᶠ n in atTop, ∃ yNeg yPos,
      yNeg ∈ S.baseBall n (2 * R) \ S.baseBall n R ∧
      yPos ∈ S.baseBall n (2 * R) \ S.baseBall n R ∧
      ¬ JoinedIn (Sigma n)ᶜ yNeg yPos) :
    let B := 2 * D + 1
    let K := {x : G.limit.carrier.carrier |
      (G.limit.flow.metric 0).edist G.limit.base x ≤ ENNReal.ofReal B}
    IsCompact K ∧ ∃ gamma : ℝ → G.limit.carrier.carrier,
      Continuous gamma ∧
      (∀ s t, (G.limit.flow.metric 0).edist (gamma s) (gamma t) =
        ENNReal.ofReal |s - t|) ∧
      (G.limit.flow.metric 0).edist G.limit.base (gamma 0) ≤ ENNReal.ofReal B ∧
      ∀ T : ℝ, 2 * B + 1 < T →
        gamma (-T) ∈ Kᶜ ∧ gamma T ∈ Kᶜ ∧ ¬ JoinedIn Kᶜ (gamma (-T)) (gamma T) := by
  classical
  let g := G.limit.flow.metric 0
  let p := G.limit.base
  let B := 2 * D + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  let : ProperSpace G.limit.carrier.carrier :=
    g.properSpace_toMetricSpace (G.limit.complete 0 G.limit.zero_mem)
  let : LocallyPathConnectedSpace G.limit.carrier.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier
  let R (j : ℕ) := 4 * ((j : ℝ) + B + R₀ + 2)
  have hR (j : ℕ) : 2 * (2 * D + 1 + 1) < R j := by
    dsimp [R, B]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hRbase (j : ℕ) : R₀ < R j := by
    dsimp [R, B]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hwindow (j : ℕ) := blowup_eventually_minimizing_window_of_annulus_separation
    G Sigma hD hSigma (hR j) (hannulus (R j) (hRbase j))
  choose index hindex using fun j => ((eventually_ge_atTop j).and (hwindow j)).exists
  choose a b arc ha hb hc hsource hcenter _hcenterS hdist _hleft _hright hnot hpreimage
    using fun j => (hindex j).2
  have hindexTop : Tendsto index atTop atTop :=
    tendsto_atTop_mono (fun j => (hindex j).1) tendsto_id
  let radius (j : ℕ) := R j / 2 - B
  have ha' (j : ℕ) : radius j ≤ a j := ha j
  have hb' (j : ℕ) : radius j ≤ b j := hb j
  have hradius : Tendsto radius atTop atTop := by
    apply tendsto_atTop_mono (f := fun j : ℕ => (j : ℝ)) _ tendsto_natCast_atTop_atTop
    intro j
    dsimp [radius, R, B]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hanchor (j : ℕ) : dist (arc j 0) p ≤ B := by
    have h := hcenter j
    change arc j 0 ∈ g.ball p (2 * D) at h
    rw [← g.toMetricSpace_ball] at h
    change dist (arc j 0) p < 2 * D at h
    change dist (arc j 0) p ≤ 2 * D + 1
    linarith
  have hdist' (j : ℕ) (s : ℝ) (hs : s ∈ Icc (-(a j)) (b j))
      (t : ℝ) (ht : t ∈ Icc (-(a j)) (b j)) :
      dist (arc j s) (arc j t) = |s - t| := by
    have h := hdist j s hs t ht
    change edist (arc j s) (arc j t) = ENNReal.ofReal |s - t| at h
    have h' := congrArg ENNReal.toReal h
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h'
  obtain ⟨gamma, hgamma, hgamma0, hconverges⟩ :=
    exists_isometric_line_of_minimizing_windows_of_bounded_anchor hanchor hradius
      (fun j s t hs ht => hdist' j s
        ⟨(neg_le_neg (ha' j)).trans (abs_le.mp hs).1, (abs_le.mp hs).2.trans (hb' j)⟩ t
        ⟨(neg_le_neg (ha' j)).trans (abs_le.mp ht).1, (abs_le.mp ht).2.trans (hb' j)⟩)
  have hpreimage' (j : ℕ) (x : G.limit.carrier.carrier)
      (hx : x ∈ (blowup_zeroSliceEmbedding G (index j)).source)
      (hxS : blowup_zeroSliceEmbedding G (index j) x ∈ Sigma (G.subsequence (index j))) :
      dist x p ≤ B := by
    have h := hpreimage j x hx hxS
    change x ∈ g.ball p (2 * D) at h
    rw [← g.toMetricSpace_ball] at h
    change dist x p < 2 * D at h
    change dist x p ≤ 2 * D + 1
    linarith
  dsimp only
  rw [← g.toMetricSpace_closedBall p (show 0 ≤ 2 * D + 1 from hB.le)]
  let K := Metric.closedBall p B
  refine ⟨isCompact_closedBall p B, gamma, hgamma.continuous, ?_, ?_, ?_⟩
  · intro s t
    change edist (gamma s) (gamma t) = _
    rw [hgamma.edist_eq, edist_dist, Real.dist_eq]
  · change edist p (gamma 0) ≤ ENNReal.ofReal B
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm] using hgamma0)
  · intro T hT
    have hTpos : 0 < T := by linarith
    have hfar (t : ℝ) (ht : |t| = T) : B < dist (gamma t) p := by
      have hd : dist (gamma t) (gamma 0) = T := by
        simpa only [Real.dist_eq, sub_zero, ht] using hgamma.dist_eq t 0
      have htri := dist_triangle (gamma t) p (gamma 0)
      rw [dist_comm p (gamma 0), hd] at htri
      linarith
    have hfarNeg := hfar (-T) (by rw [abs_neg, abs_of_pos hTpos])
    have hfarPos := hfar T (abs_of_pos hTpos)
    refine ⟨not_le.mpr hfarNeg, not_le.mpr hfarPos, ?_⟩
    intro hjoined
    obtain ⟨VNeg, hVNegOpen, hVNegBase, hVNegPath, hVNegCompact, hVNegOutside⟩ :=
      exists_precompact_pathConnected_nhds_outside_closedBall hfarNeg
    obtain ⟨VPos, hVPosOpen, hVPosBase, hVPosPath, hVPosCompact, hVPosOutside⟩ :=
      exists_precompact_pathConnected_nhds_outside_closedBall hfarPos
    let beta := hjoined.somePath
    let Q := (closure VNeg ∪ range beta) ∪ closure VPos
    have hQcompact : IsCompact Q :=
      (hVNegCompact.union (isCompact_range beta.continuous)).union hVPosCompact
    have hQoutside : Q ⊆ Kᶜ := by
      rintro x ((hx | ⟨t, rfl⟩) | hx)
      · exact hVNegOutside hx
      · exact hjoined.somePath_mem t
      · exact hVPosOutside hx
    obtain ⟨stage, hstage⟩ := blowup_exists_exhaustion_superset G hQcompact
    have hdomain : ∀ᶠ j in atTop, Q ⊆ (blowup_zeroSliceEmbedding G (index j)).source := by
      filter_upwards [hindexTop.eventually (eventually_ge_atTop stage)] with j hj
      rw [blowup_zeroSliceEmbedding_source]
      exact hstage.trans (G.exhaustion.space_increasing hj)
    have hnearNeg : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), arc j (-T) ∈ VNeg :=
      (hconverges (-T)).eventually (hVNegOpen.mem_nhds hVNegBase)
    have hnearPos : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), arc j T ∈ VPos :=
      (hconverges T).eventually (hVPosOpen.mem_nhds hVPosBase)
    have hgood : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ),
        Q ⊆ (blowup_zeroSliceEmbedding G (index j)).source ∧
        arc j (-T) ∈ VNeg ∧ arc j T ∈ VPos ∧ T ≤ radius j := by
      filter_upwards [hdomain.filter_mono Nat.hyperfilter_le_atTop, hnearNeg, hnearPos,
        (hradius.eventually_ge_atTop T).filter_mono Nat.hyperfilter_le_atTop]
        with j hj hneg hpos hrad
      exact ⟨hj, hneg, hpos, hrad⟩
    obtain ⟨j, hjdomain, hjNeg, hjPos, hjradius⟩ := hgood.exists
    let e : OpenPartialHomeomorph G.limit.carrier.carrier
        ((S.flow (G.subsequence (index j))).slice
          (S.base (G.subsequence (index j))).1).carrier :=
      blowup_zeroSliceEmbedding G (index j)
    have htruncated := window_truncation_not_joined e (hc j) (hsource j)
      (hdist' j) (hanchor j) (hpreimage' j) (hnot j) hB.le hT
      (hjradius.trans (ha' j)) (hjradius.trans (hb' j))
    have hattachNeg : JoinedIn Q (arc j (-T)) (gamma (-T)) :=
      (hVNegPath.joinedIn _ hjNeg _ hVNegBase).mono
        (fun x hx => Or.inl (Or.inl (subset_closure hx)))
    have hbeta : JoinedIn Q (gamma (-T)) (gamma T) :=
      ⟨beta, fun t => Or.inl (Or.inr (mem_range_self t))⟩
    have hattachPos : JoinedIn Q (gamma T) (arc j T) :=
      (hVPosPath.joinedIn _ hVPosBase _ hjPos).mono (fun x hx => Or.inr (subset_closure hx))
    have hpath := ((hattachNeg.trans hbeta).trans hattachPos).map_continuousOn
      (e.continuousOn.mono hjdomain)
    apply htruncated
    apply hpath.mono
    rintro y ⟨x, hx, rfl⟩ hxS
    exact hQoutside hx (hpreimage' j x (hjdomain hx) hxS)

end PoincareConjecture.M32
