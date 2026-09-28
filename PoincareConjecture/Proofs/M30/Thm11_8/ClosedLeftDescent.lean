import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.FiniteChartDescent
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Measure.Monotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Pointed
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Completeness
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Calculus
import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.secondCountable

theorem exists_closed_left_flow_of_local_extensions
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ} (hT : 0 < T)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (hlocal : ∀ A : ℝ, 0 < A →
      ∀ U : TopologicalSpace.Opens G.limit.carrier.carrier,
        (U : Set G.limit.carrier.carrier) =
          (G.limit.flow.metric 0).ball G.limit.base A →
        ∃ delta : ℝ, 0 < delta ∧
          ∃ P : RicciFlow 3 U (Icc (-(T + delta)) 0),
            (∀ t ∈ Ioc (-T) 0, ∀ (x : U)
              (v w : TangentSpace (𝓡 3) x),
              (P.metric t).inner x v w =
                (G.limit.flow.metric t).inner x.val
                  (mfderiv (𝓡 3) (𝓡 3)
                    (Subtype.val : U → G.limit.carrier.carrier) x v)
                  (mfderiv (𝓡 3) (𝓡 3)
                    (Subtype.val : U → G.limit.carrier.carrier) x w)) ∧
            ∀ t ∈ Icc (-(T + delta)) 0, ∀ x : U,
              (P.connection t).NonnegativeCurvatureOperator x) :
    ∃ Fbar : RicciFlow 3 G.limit.carrier.carrier (Icc (-T) 0),
      (∀ t ∈ Ioc (-T) 0, Fbar.metric t = G.limit.flow.metric t) ∧
      (∀ t ∈ Icc (-T) 0,
        G.limit.carrier.metricComplete (Fbar.metric t)) ∧
      (∀ t ∈ Icc (-T) 0, ∀ x : G.limit.carrier.carrier,
        (Fbar.connection t).NonnegativeCurvatureOperator x) ∧
      (∀ (x : G.limit.carrier.carrier) (v : TangentSpace (𝓡 3) x),
        (G.limit.flow.metric 0).inner x v v ≤
          (Fbar.metric (-T)).inner x v v) ∧
      ∀ A : ℝ, 0 < A →
      ∀ U : TopologicalSpace.Opens G.limit.carrier.carrier,
        (U : Set G.limit.carrier.carrier) =
          (G.limit.flow.metric 0).ball G.limit.base A →
        ∃ delta : ℝ, 0 < delta ∧
          ∃ P : RicciFlow 3 U (Icc (-(T + delta)) 0),
            (∀ t ∈ Icc (-T) 0, ∀ (x : U)
              (v w : TangentSpace (𝓡 3) x),
              (P.metric t).inner x v w =
                (Fbar.metric t).inner x.val
                  (mfderiv (𝓡 3) (𝓡 3)
                    (Subtype.val : U → G.limit.carrier.carrier) x v)
                  (mfderiv (𝓡 3) (𝓡 3)
                    (Subtype.val : U → G.limit.carrier.carrier) x w)) ∧
            ∀ t ∈ Icc (-(T + delta)) 0, ∀ x : U,
              (P.connection t).NonnegativeCurvatureOperator x := by
  classical
  let M := G.limit.carrier.carrier
  let g0 : RiemannianMetric 3 M := G.limit.flow.metric 0
  let p : M := G.limit.base
  have htime : -T < 0 := by linarith
  have hballopen (r : ℝ) : IsOpen (g0.ball p r) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g0.toRiemannianMetric⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    change IsOpen {x : M | edist p x < ENNReal.ofReal r}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let U (j : ℕ) : TopologicalSpace.Opens M :=
    ⟨g0.ball p (j + 1), hballopen (j + 1)⟩
  let q (j : ℕ) : U j → M := Subtype.val
  have hq (j : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q j) := by
    exact Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U j)
  let : ConnectedSpace M := G.limit.connectedSpace
  have hcover (x : M) : ∃ j z, q j z = x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g0.toRiemannianMetric⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    have hfin : edist p x ≠ (⊤ : ℝ≥0∞) :=
      @Poincare.edist_ne_top_of_preconnected M _ _ p x
    obtain ⟨j, hj⟩ := exists_nat_gt (ENNReal.toReal (edist p x))
    refine ⟨j, ⟨x, ?_⟩, rfl⟩
    change edist p x < ENNReal.ofReal (j + 1)
    rw [ENNReal.lt_ofReal_iff_toReal_lt hfin]
    linarith
  choose delta hdelta P hPmetric hPsign using fun j : ℕ =>
    hlocal (j + 1) (by positivity : (0 : ℝ) < j + 1) (U j) (by rfl)
  have hsub (j : ℕ) : Icc (-T) 0 ⊆ Icc (-(T + delta j)) 0 := by
    intro t ht
    constructor
    · calc
        -(T + delta j) ≤ -T := by linarith [hdelta j]
        _ ≤ t := ht.1
    · exact ht.2
  let Fchart (j : ℕ) : RicciFlow 3 (U j) (Icc (-T) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow (P j) (hsub j)
      ordConnected_Icc ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
  let Fint : RicciFlow 3 M (Ioo (-T) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.limit.flow
      Ioo_subset_Ioc_self ordConnected_Ioo
      ⟨-T / 2, ⟨by linarith, by linarith⟩, -T / 3, ⟨by linarith, by linarith⟩,
        by linarith⟩
  have hinterior (t : ℝ) (ht : t ∈ Ioo (-T) 0) (j : ℕ) (x : U j)
      (v w : TangentSpace (𝓡 3) x) :
      ((Fchart j).metric t).inner x v w = (Fint.metric t).inner (q j x)
        (mfderiv (𝓡 3) (𝓡 3) (q j) x v)
        (mfderiv (𝓡 3) (𝓡 3) (q j) x w) := by
    simpa only [Fchart, Fint, q, Poincare.Geometry.RicciFlow.Harnack.restrictFlow]
      using hPmetric j t (Ioo_subset_Ioc_self ht) x v w
  obtain ⟨Fbar, hFinterior, hFchart⟩ :=
    exists_finite_extension_of_covering_chart_flows (n := 3) (ι := ℕ)
      (U := fun j => U j) (M := M) (show -T < 0 by linarith)
      Fint Fchart q hq hcover hinterior
  have hmetric_ext (g₁ g₂ : RiemannianMetric 3 M)
      (hinner : g₁.inner = g₂.inner) : g₁ = g₂ := by
    cases g₁
    cases g₂
    cases hinner
    rfl
  have hpast (t : ℝ) (ht : t ∈ Ioc (-T) 0) :
      Fbar.metric t = G.limit.flow.metric t := by
    apply hmetric_ext
    funext x
    ext v w
    have heq : EqOn (fun s => (Fbar.metric s).inner x v w)
        (fun s => (G.limit.flow.metric s).inner x v w) (Ioo (-T) 0) := by
      intro s hs
      change (Fbar.metric s).inner x v w = (G.limit.flow.metric s).inner x v w
      rw [hFinterior s hs]
      rfl
    have hleft : ContinuousOn (fun s => (Fbar.metric s).inner x v w)
        (Ioc (-T) 0) := by
      intro s hs
      exact ((Fbar.equation s ⟨le_of_lt hs.1, hs.2⟩ x v w).continuousWithinAt).mono
        (fun z hz => ⟨le_of_lt hz.1, hz.2⟩)
    have hright : ContinuousOn (fun s => (G.limit.flow.metric s).inner x v w)
        (Ioc (-T) 0) := by
      intro s hs
      exact (G.limit.flow.equation s hs x v w).continuousWithinAt
    exact heq.of_subset_closure hleft hright
      (fun s hs => ⟨hs.1, hs.2.le⟩)
      (by rw [closure_Ioo htime.ne]; exact fun s hs => ⟨le_of_lt hs.1, hs.2⟩) ht
  have hzero : Fbar.metric 0 = g0 := by
    rw [hpast 0 ⟨by linarith, le_rfl⟩]
  have hoperator (t : ℝ) (ht : t ∈ Icc (-T) 0) (x : M) :
      (Fbar.connection t).NonnegativeCurvatureOperator x := by
    obtain ⟨j, z, rfl⟩ := hcover x
    exact (((Fchart j).connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
      (Fbar.connection t) isOpen_univ (hq j).contMDiff.contMDiffOn
      (fun y _ v w => hFchart t ht j y v w) (mem_univ z)).mp
      (hPsign j t (hsub j ht) z)
  have hdom (x : M) (v : TangentSpace (𝓡 3) x) :
      g0.inner x v v ≤ (Fbar.metric (-T)).inner x v v := by
    have hric : ∀ t ∈ Icc (-T) 0, ∀ z : M,
        ∀ w : TangentSpace (𝓡 3) z, 0 ≤ (Fbar.connection t).ricci z w w := by
      intro t ht z w
      exact ((Fbar.connection t).ricci_bounds_of_nonnegative_curvatureOperator
        ((Fbar.connection t).normalization_curvatureTensorCalculus) z
        (hoperator t ht z) w).1
    have h := PoincareConjecture.RicciFlow.inner_antitone_of_nonnegative_ricci Fbar
      (convex_Icc (-T) 0) hric ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
      (by linarith) x v
    simpa only [hzero] using h
  have hEndComplete : G.limit.carrier.metricComplete (Fbar.metric (-T)) := by
    let d₀ := (G.limit.carrier.metricEMetricSpace g0).toPseudoEMetricSpace
    let d₁ := (G.limit.carrier.metricEMetricSpace (Fbar.metric (-T))).toPseudoEMetricSpace
    change @CompleteSpace M d₁.toUniformSpace
    apply Poincare.completeSpace_of_continuous_local_edist_bound d₀ d₁ p
      (G.limit.complete 0 G.limit.zero_mem)
    · change @Continuous M M G.limit.carrier.topologicalSpace
        G.limit.carrier.topologicalSpace id
      exact continuous_id
    · exact fun x => @Poincare.edist_ne_top_of_preconnected M d₁
        (G.limit.carrier.preconnected_metricEMetricSpace (Fbar.metric (-T))) x p
    · intro R
      let r : ℝ := R + 1
      have hr : 0 < r := by dsimp [r]; positivity
      have hR : (R : ℝ≥0∞) < ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by dsimp [r]; linarith)
      have hmem (z : M) (hz : d₁.edist z p ≤ R) :
          z ∈ (Fbar.metric (-T)).ball p r := by
        change d₁.edist p z < ENNReal.ofReal r
        rw [d₁.edist_comm]
        exact hz.trans_lt hR
      refine ⟨Real.toNNReal 1, fun x y hx hy => ?_⟩
      change g0.edist x y ≤ ENNReal.ofReal (1 : ℝ) *
        (Fbar.metric (-T)).edist x y
      simpa only [ENNReal.ofReal_one, one_mul] using
        (RiemannianMetric.edist_le_mul_edist_of_tangentNorm_le_on_ball
          (Fbar.metric (-T)) g0 p r 1 hr one_pos
          (fun z _ w => by
            have hsqrt := Real.sqrt_le_sqrt (hdom z w)
            simpa only [RiemannianMetric.tangentNorm, one_mul] using hsqrt)
          (hmem x hx) (hmem y hy))
  have hcomplete (t : ℝ) (ht : t ∈ Icc (-T) 0) :
      G.limit.carrier.metricComplete (Fbar.metric t) := by
    by_cases hleft : t = -T
    · simpa only [hleft] using hEndComplete
    · have ht' : t ∈ Ioc (-T) 0 := ⟨lt_of_le_of_ne ht.1 (Ne.symm hleft), ht.2⟩
      rw [hpast t ht']
      exact G.limit.complete t ht'
  refine ⟨Fbar, ?_, ?_, ?_, hdom, ?_⟩
  · intro t ht
    exact hpast t ht
  · intro t ht
    exact hcomplete t ht
  · exact hoperator
  · intro A hA V hV
    obtain ⟨delta, hdelta, P, hPmetric, hPsign⟩ := hlocal A hA V hV
    refine ⟨delta, hdelta, P, ?_, hPsign⟩
    intro t ht x v w
    have hsubV : Icc (-T) 0 ⊆ Icc (-(T + delta)) 0 := by
      intro s hs
      exact ⟨(by
        calc
          -(T + delta) ≤ -T := by linarith [hdelta]
          _ ≤ s := hs.1), hs.2⟩
    have heq : EqOn (fun s => (P.metric s).inner x v w)
        (fun s => (Fbar.metric s).inner x.val
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : V → G.limit.carrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : V → G.limit.carrier.carrier) x w)) (Ioo (-T) 0) := by
      intro s hs
      change (P.metric s).inner x v w = (Fbar.metric s).inner x.val
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : V → G.limit.carrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : V → G.limit.carrier.carrier) x w)
      rw [hPmetric s (Ioo_subset_Ioc_self hs), ← hpast s ⟨hs.1, hs.2.le⟩]
    have hleft : ContinuousOn (fun s => (P.metric s).inner x v w)
        (Icc (-T) 0) := by
      intro s hs
      exact ((P.equation s (hsubV hs) x v w).continuousWithinAt).mono hsubV
    have hright : ContinuousOn (fun s => (Fbar.metric s).inner x.val
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : V → G.limit.carrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : V → G.limit.carrier.carrier) x w)) (Icc (-T) 0) := by
      intro s hs
      exact ((Fbar.equation s hs x.val
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : V → G.limit.carrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : V → G.limit.carrier.carrier) x w)).continuousWithinAt)
    exact heq.of_subset_closure hleft hright Ioo_subset_Icc_self
      (by rw [closure_Ioo (ne_of_lt htime)]) ht

end PoincareConjecture.M30
