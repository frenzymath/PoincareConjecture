import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedScalarConvergence
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedMetricComparison
import PoincareConjecture.Proofs.M30.Generalized.TerminalMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.M28.Generalized.CanonicalAdapters
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal
import PoincareConjecture.Statements.M30Providers
import Mathlib.Topology.Order.IntermediateValue













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

set_option maxHeartbeats 800000 in





theorem exists_compact_limit_scalar_bound_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ),
        0 < epsilon → epsilon ≤ epsilon0 → 0 < C →
        GeneralizedBoundedDistanceHypotheses S epsilon C →
      ∀ (T : ℝ), 0 < T →
      ∀ (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
        (X : Set G.limit.carrier.carrier),
        IsCompact X → IsConnected X →
      ∀ L Cmin : ℝ,
        (∀ t ∈ Ioc (-T) 0, ∀ x ∈ X, ∀ y ∈ X,
          ((G.limit.flow.metric t).edist x y).toReal ≤ L) →
        (∀ t ∈ Ioc (-T) 0, ∃ y ∈ X,
          (G.limit.flow.connection t).scalarCurvature y ≤ Cmin) →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (-T) 0, ∀ x ∈ X,
          (G.limit.flow.connection t).scalarCurvature x ≤ B := by
  classical
  obtain ⟨epsilon0, hepsilon0, hepsilonMax, hbounded⟩ := P.m29.constants
  refine ⟨epsilon0, hepsilon0, hepsilonMax, ?_⟩
  intro S epsilon C hepsilon hepsilonLe hC H T hT G X hX hXconnected L Cmin hdiam hmin
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  have hzero : (0 : ℝ) ∈ Ioc (-T) 0 := ⟨by linarith, le_rfl⟩
  obtain ⟨a0, ha0, _ha0scalar⟩ := hmin 0 hzero
  have hL : 0 ≤ L := ENNReal.toReal_nonneg.trans (hdiam 0 hzero a0 ha0 a0 ha0)
  let c := max 2 Cmin
  have hc : 2 ≤ c := le_max_left _ _
  have hcpos : 0 < c := by linarith
  by_contra hboundedLimit
  push Not at hboundedLimit
  have hunbounded (m : ℕ) : ∃ t ∈ Ioc (-T) 0,
      ∃ z ∈ X, (c + 1) * ((m : ℝ) + 2) <
        (G.limit.flow.connection t).scalarCurvature z := by
    exact hboundedLimit ((c + 1) * ((m : ℝ) + 2)) (by positivity)
  choose t ht z hz hhigh using hunbounded
  have hlevel (m : ℕ) : ∃ y ∈ X, (G.limit.flow.connection (t m)).scalarCurvature y = c := by
    obtain ⟨a, ha, hRa⟩ := hmin (t m) (ht m)
    have hregular := (P.m04.scalar_regular 3 G.limit.carrier.carrier
      (Ioc (-T) 0) G.limit.flow).continuousOn
    have hcont : ContinuousOn (G.limit.flow.connection (t m)).scalarCurvature X := by
      have hmap : Continuous (fun x : G.limit.carrier.carrier => (t m, x)) :=
        continuous_const.prodMk continuous_id
      exact ContinuousOn.comp
        (f := fun x : G.limit.carrier.carrier => (t m, x))
        (g := fun p : ℝ × G.limit.carrier.carrier =>
          (G.limit.flow.connection p.1).scalarCurvature p.2)
        hregular hmap.continuousOn (fun x _ => ⟨ht m, mem_univ x⟩)
    apply hXconnected.2.intermediate_value ha (hz m) hcont
    refine ⟨hRa.trans (le_max_right _ _), ?_⟩
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [hhigh m]
  choose y hy hyR using hlevel
  let g := fun m => G.limit.flow.metric (t m)
  let K := fun m => {x | (g m).edist (y m) x ≤ ENNReal.ofReal (L + 1)}
  have hK (m : ℕ) : IsCompact (K m) :=
    (g m).isCompact_closedBall_of_metricComplete (G.limit.complete (t m) (ht m))
      (y m) (L + 1)
  have hball (m : ℕ) : (g m).ball (y m) (L + 1) ⊆ K m := by
    intro x hx
    change (g m).edist (y m) x < ENNReal.ofReal (L + 1) at hx
    exact hx.le
  have hzball (m : ℕ) : z m ∈ (g m).ball (y m) (L + 1) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt ((g m).edist_ne_top (y m) (z m))).mpr
    have h := hdiam (t m) (ht m) (y m) (hy m) (z m) (hz m)
    change ((g m).edist (y m) (z m)).toReal ≤ L at h
    linarith
  let Q : ℕ → ℕ → Prop := fun m k =>
    ∃ htime : t m ∈ Icc (-G.exhaustion.time k) 0,
      K m ⊆ G.exhaustion.space k ∧
      (∀ x ∈ K m, ∀ v : TangentSpace (𝓡 3) x,
        let e := generalizedSliceHomeomorph G k (t m) htime
        (normalizedBlowupSliceMetric S (G.subsequence k) (t m)).tangentNorm
          (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤ 2 * (g m).tangentNorm x v) ∧
      (∀ x ∈ X,
        |(S.flow (G.subsequence k)).scalar ((G.embedding k).pointMap (t m) htime x) /
            S.scale (G.subsequence k) -
          (G.limit.flow.connection (t m)).scalarCurvature x| < 1 / 2)
  have hQevent (m : ℕ) : ∀ᶠ k in atTop, Q m k := by
    obtain ⟨N, hN⟩ := exists_generalized_time_shift G (ht m)
    have hmetric := eventually_generalized_tangent_comparison G (ht m) N hN
      (hK m) (show (1 : ℝ) < 2 by norm_num)
    obtain ⟨j, hj⟩ := eventually_atTop.mp hmetric
    have hscalar := eventually_generalized_scalar_error G isCompact_singleton
      (singleton_subset_iff.mpr (ht m)) hX (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hscalar, eventually_ge_atTop (j + N)] with k hk hlarge
    have hNk : N ≤ k := by omega
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hNk
    have hcomp := hj i (by omega)
    let htime := hk.1 (mem_singleton (t m))
    exact ⟨htime, hcomp.1, fun x hx v => (hcomp.2 x hx v).1,
      fun x hx => hk.2.2 (t m) (mem_singleton (t m)) htime x hx⟩
  obtain ⟨sigma, hsigma, hselected⟩ :=
    Poincare.exists_strictMono_forall_le_of_eventually hQevent
  have hself (m : ℕ) := hselected m m le_rfl
  choose htime hcontain htan herror using hself
  let n := fun m => G.subsequence (sigma m)
  let p := fun m => (G.embedding (sigma m)).pointMap (t m) (htime m) (y m)
  let q := fun m => (G.embedding (sigma m)).pointMap (t m) (htime m) (z m)
  let Rnew := fun m => (S.flow (n m)).scalar (p m)
  have hscale (m : ℕ) : (c - 1 / 2) * S.scale (n m) < Rnew m ∧
      Rnew m < (c + 1 / 2) * S.scale (n m) := by
    have h := herror m (y m) (hy m)
    rw [hyR m] at h
    change |Rnew m / S.scale (n m) - c| < 1 / 2 at h
    obtain ⟨hlo, hhi⟩ := abs_lt.mp h
    have hQpos : 0 < S.scale (n m) := S.base_scalar_pos (n m)
    have hlo' : c - 1 / 2 < Rnew m / S.scale (n m) := by linarith only [hlo]
    have hhi' : Rnew m / S.scale (n m) < c + 1 / 2 := by linarith only [hhi]
    exact ⟨(lt_div_iff₀ hQpos).mp hlo', (div_lt_iff₀ hQpos).mp hhi'⟩
  have hlower (m : ℕ) : S.scale (n m) ≤ Rnew m := by
    calc
      S.scale (n m) = 1 * S.scale (n m) := (one_mul _).symm
      _ ≤ (c - 1 / 2) * S.scale (n m) :=
        mul_le_mul_of_nonneg_right (by linarith) (S.base_scalar_pos (n m)).le
      _ ≤ Rnew m := (hscale m).1.le
  have hRpos (m : ℕ) : 0 < Rnew m := (S.base_scalar_pos (n m)).trans_le (hlower m)
  have hupper (m : ℕ) : Rnew m ≤ (c + 1) * S.scale (n m) :=
    (hscale m).2.le.trans
      (mul_le_mul_of_nonneg_right (by linarith) (S.base_scalar_pos (n m)).le)
  have hdiverges : Tendsto (fun m => S.scale (n m)) atTop atTop :=
    S.scalar_diverges.comp (G.subsequence_strictMono.comp hsigma).tendsto_atTop
  let S' : GeneralizedBlowupSequence.{u} := {
    flow := fun m => S.flow (n m)
    base := p
    base_scalar_pos := hRpos
    scalar_diverges := tendsto_atTop_mono hlower hdiverges }
  have H' : GeneralizedBoundedDistanceHypotheses S' epsilon C := {
    branch := fun m => H.branch (n m)
    canonical := by
      intro m
      have hphysical : (p m).1 ≤ (S.base (n m)).1 :=
        add_le_of_nonpos_right
          (div_nonpos_of_nonpos_of_nonneg (ht m).2 (S.base_scalar_pos (n m)).le)
      exact (H.canonical (n m)).rebase hphysical (hlower m) }
  let c0 := 2 * Real.sqrt (c + 1)
  have hc0 : 0 < c0 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by linarith))
  let Astar := c0 * (L + 1) + 1
  have hAstar : 0 < Astar := by dsimp [Astar]; positivity
  have hcapture (m : ℕ) : (q m).2 ∈ S'.baseBall m Astar := by
    let e := generalizedSliceHomeomorph G (sigma m) (t m) (htime m)
    let hnew : RiemannianMetric 3 ((S'.flow m).slice (S'.base m).1).carrier :=
      M13.scaleSmoothMetric ((S'.flow m).metric (S'.base m).1)
      (S'.scale m) (S'.base_scalar_pos m)
    let graw := (S.flow (n m)).metric ((S.base (n m)).1 + t m / S.scale (n m))
    have hsource : (g m).ball (y m) (L + 1) ⊆ e.source :=
      fun x hx => hcontain m (hball m hx)
    have he : ∀ x ∈ e.source, ContMDiffAt (𝓡 3) (𝓡 3) 1 e x :=
      fun x hx => (generalizedSliceHomeomorph_contMDiffAt G (sigma m) (t m)
        (htime m) hx).of_le (by norm_num)
    have hnorm : ∀ x ∈ (g m).ball (y m) (L + 1), ∀ v : TangentSpace (𝓡 3) x,
        hnew.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
          c0 * (g m).tangentNorm x v := by
      intro x hx v
      have hroot : Real.sqrt (Rnew m) ≤ Real.sqrt (c + 1) * Real.sqrt (S.scale (n m)) :=
        (Real.sqrt_le_sqrt (hupper m)).trans_eq (Real.sqrt_mul (by linarith) _)
      have hraw : 0 ≤ graw.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) :=
        Real.sqrt_nonneg _
      calc
        hnew.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) =
            Real.sqrt (Rnew m) * graw.tangentNorm (e x)
              (mfderiv (𝓡 3) (𝓡 3) e x v) :=
          M13.scaleSmoothMetric_tangentNorm _ _ _ _ _
        _ ≤ (Real.sqrt (c + 1) * Real.sqrt (S.scale (n m))) *
            graw.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) :=
          mul_le_mul_of_nonneg_right hroot hraw
        _ = Real.sqrt (c + 1) *
            (normalizedBlowupSliceMetric S (n m) (t m)).tangentNorm
              (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) := by
          rw [normalizedBlowupSliceMetric, M13.scaleSmoothMetric_tangentNorm]
          ring
        _ ≤ Real.sqrt (c + 1) * (2 * (g m).tangentNorm x v) :=
          mul_le_mul_of_nonneg_left (htan m x (hball m hx) v) (Real.sqrt_nonneg _)
        _ = c0 * (g m).tangentNorm x v := by dsimp [c0]; ring
    have himage := (g m).image_ball_subset_ball_of_tangentNorm_le hnew e (y m)
      hc0 hsource he hnorm
    have hq := himage (mem_image_of_mem e (hzball m))
    rw [← scaled_terminal_ball_eq_baseBall S' m Astar]
    change hnew.edist (e (y m)) (e (z m)) < ENNReal.ofReal Astar
    exact hq.trans_le (ENNReal.ofReal_le_ofReal (by dsimp [Astar]; linarith))
  obtain ⟨D, _hD, hDtail⟩ := hbounded epsilon hepsilon hepsilonLe C hC S' H' Astar hAstar
  have hlargeScalar (m : ℕ) : ((m : ℝ) + 1) * Rnew m <
      (S.flow (n m)).scalar (q m) := by
    have h := (abs_lt.mp (herror m (z m) (hz m))).1
    have hratio : (c + 1) * ((m : ℝ) + 1) <
        (S.flow (n m)).scalar (q m) / S.scale (n m) := by
      change -(1 / 2 : ℝ) < (S.flow (n m)).scalar (q m) / S.scale (n m) -
        (G.limit.flow.connection (t m)).scalarCurvature (z m) at h
      nlinarith [hhigh m]
    have hmul := (lt_div_iff₀ (S.base_scalar_pos (n m))).mp hratio
    calc
      ((m : ℝ) + 1) * Rnew m ≤
          ((m : ℝ) + 1) * ((c + 1) * S.scale (n m)) :=
        mul_le_mul_of_nonneg_left (hupper m) (by positivity)
      _ = ((c + 1) * ((m : ℝ) + 1)) * S.scale (n m) := by ring
      _ < (S.flow (n m)).scalar (q m) := hmul
  obtain ⟨N, hN⟩ := exists_nat_gt D
  obtain ⟨m, hm, hmN⟩ := (hDtail.and (eventually_ge_atTop N)).exists
  have hbound := hm (q m).2 (hcapture m)
  change (S.flow (n m)).scalar (q m) ≤ D * Rnew m at hbound
  have hDm : D < (m : ℝ) + 1 := by
    have hNm : (N : ℝ) ≤ m := Nat.cast_le.mpr hmN
    linarith
  have hproduct := mul_lt_mul_of_pos_right hDm (hRpos m)
  linarith [hlargeScalar m]

end PoincareConjecture.M30
