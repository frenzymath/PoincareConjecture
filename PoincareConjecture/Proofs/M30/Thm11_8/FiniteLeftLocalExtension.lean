import PoincareConjecture.Proofs.M30.Thm11_8.FiniteLeftSourceFlows
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteLeftStageLimit
import PoincareConjecture.Proofs.M30.Thm11_8.ClosedLeftDescent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

private theorem finiteLeftStage_openCodomain
    {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z]
    (U : TopologicalSpace.Opens Z) (e : X → U)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((Subtype.val : U → Z) ∘ e)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := by
  have hU := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U
  intro x
  have hix := hU (e x)
  apply ((he x).comp (𝓡 3) U hix.localInverse_isLocalDiffeomorphAt).congr_of_eventuallyEq
  filter_upwards [(he x).contMDiffAt.continuousAt.preimage_mem_nhds
    (hix.localInverse.open_source.mem_nhds hix.localInverse_mem_source)] with y hy
  exact Subtype.ext (hix.localInverse_right_inv hy).symm

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 1800000 in



theorem exists_nonnegative_left_extension_on_stage
    (hShi : LocalCurvatureDerivativeEstimates.{u})
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ} (hT : 0 < T)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (hbranch : ∀ k, generalizedPinchedOrNonnegative (S.flow k))
    (hcompact : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (S.baseBall (G.subsequence k) A)))
    (hcyl : ∀ A : ℝ, 0 < A →
      ∃ delta : ℝ, 0 < delta ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (G.subsequence k)
            A (T + delta) B 1))
    (Y Yplus : TopologicalSpace.Opens G.limit.carrier.carrier)
    (hY : IsCompact (closure (Y : Set G.limit.carrier.carrier)))
    (hYne : (Y : Set G.limit.carrier.carrier).Nonempty)
    (hYplus : IsCompact (closure (Yplus : Set G.limit.carrier.carrier)))
    (hbuffer : closure (Y : Set G.limit.carrier.carrier) ⊆ Yplus) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ F : RicciFlow 3 Y (Icc (-(T + delta)) 0),
      (∀ t ∈ Ioc (-T) 0, ∀ (x : Y) (v w : TangentSpace (𝓡 3) x),
        (F.metric t).inner x v w = (G.limit.flow.metric t).inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Y → G.limit.carrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Y → G.limit.carrier.carrier) x w)) ∧
      ∀ t ∈ Icc (-(T + delta)) 0, ∀ x : Y,
        (F.connection t).NonnegativeCurvatureOperator x := by
  classical
  obtain ⟨W, delta, B, _, hdelta, _, N, E, f, P,
      _hf, hstage, _hzero, _hball, _hpull, _hnative, hmatch, hcurv, hdefect⟩ :=
    exists_extended_source_flows_on_generalized_stage hShi hT G hbranch hcompact hcyl
      Yplus hYplus
  let tau := T + delta / 2
  have hTtau : T < tau := by dsimp [tau]; linarith
  have htau : 0 < tau := hT.trans hTtau
  have hJsub : Icc (-tau) 0 ⊆ Icc (-(T + delta)) 0 := by
    intro t ht
    exact ⟨by dsimp [tau] at ht; linarith [ht.1], ht.2⟩
  have hJne : (Icc (-tau) (0 : ℝ)).Nontrivial :=
    ⟨-tau, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
  let P0 (k : ℕ) : RicciFlow 3 Yplus (Icc (-tau) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow (P k) hJsub ordConnected_Icc hJne
  have hstage0 (k : ℕ) : (Yplus : Set G.limit.carrier.carrier) ⊆
      G.exhaustion.space (k + N) := subset_closure.trans (hstage k)
  have hmatch0 : ∀ k s (_hs : s ∈ Icc (-tau) 0)
      (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0)
      (x : Yplus) (v w : TangentSpace (𝓡 3) x),
      ((P0 k).metric s).inner x v w =
        (G.embedding (k + N)).pullbackInner s hsG x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Yplus → G.limit.carrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Yplus → G.limit.carrier.carrier) x w) :=
    fun k s hs hsG x v w => hmatch k s (hJsub hs) hsG x v w
  have hdefect0 (eta : ℝ) (heta : 0 < eta) : ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Icc (-tau) 0, ∀ x : Yplus,
        ((P0 k).connection t).negativeCurvaturePart x ≤ eta :=
    (hdefect eta heta).mono fun k hk t ht x => hk t (hJsub ht) x
  obtain ⟨L⟩ := exists_finiteLeftStageLimit hT hTtau G Yplus N P0
    hstage0 hmatch0 hcurv hdefect0 (closure (Y : Set G.limit.carrier.carrier))
    hY (hYne.mono subset_closure) hbuffer
  let inc : Y → L.domain := fun x => ⟨x.val, L.contains (subset_closure x.property)⟩
  have hinc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ inc :=
    finiteLeftStage_openCodomain L.domain inc
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y)
  have hLinc := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) L.domain
  let F : RicciFlow 3 Y (Icc (-tau) 0) := L.flow.pullbackWithConnection inc hinc
    (fun t => ((L.flow.metric t).pullbackOfLocalDiffeomorph inc hinc).leviCivitaData)
  refine ⟨delta / 2, half_pos hdelta, F, ?_, ?_⟩
  · intro t ht x v w
    change (L.flow.metric t).inner (inc x)
      (mfderiv (𝓡 3) (𝓡 3) inc x v) (mfderiv (𝓡 3) (𝓡 3) inc x w) = _
    rw [L.interior_metric t ht]
    have hd := mfderiv_comp x ((hLinc (inc x)).mdifferentiableAt (by simp))
      ((hinc x).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Y → G.limit.carrier.carrier) x =
      (mfderiv (𝓡 3) (𝓡 3)
        (Subtype.val : L.domain → G.limit.carrier.carrier) (inc x)).comp
          (mfderiv (𝓡 3) (𝓡 3) inc x) at hd
    exact congrArg₂ (fun a b => (G.limit.flow.metric t).inner x.val a b)
      (congrArg (fun A => A v) hd).symm (congrArg (fun A => A w) hd).symm
  · intro t ht x
    exact ((F.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
      (L.flow.connection t) isOpen_univ hinc.contMDiff.contMDiffOn
      (fun _ _ _ _ => rfl) (mem_univ x)).mpr (L.nonnegative t ht (inc x))



theorem exists_nonnegative_left_extension_on_terminal_ball
    (hShi : LocalCurvatureDerivativeEstimates.{u})
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ} (hT : 0 < T)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (hbranch : ∀ k, generalizedPinchedOrNonnegative (S.flow k))
    (hcompact : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (S.baseBall (G.subsequence k) A)))
    (hcyl : ∀ A : ℝ, 0 < A →
      ∃ delta : ℝ, 0 < delta ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (G.subsequence k)
            A (T + delta) B 1))
    (A : ℝ) (hA : 0 < A)
    (Y : TopologicalSpace.Opens G.limit.carrier.carrier)
    (hY : (Y : Set G.limit.carrier.carrier) =
      (G.limit.flow.metric 0).ball G.limit.base A) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ F : RicciFlow 3 Y (Icc (-(T + delta)) 0),
      (∀ t ∈ Ioc (-T) 0, ∀ (x : Y) (v w : TangentSpace (𝓡 3) x),
        (F.metric t).inner x v w = (G.limit.flow.metric t).inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Y → G.limit.carrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Y → G.limit.carrier.carrier) x w)) ∧
      ∀ t ∈ Icc (-(T + delta)) 0, ∀ x : Y,
        (F.connection t).NonnegativeCurvatureOperator x := by
  let g := G.limit.flow.metric 0
  let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
  have hball (r : ℝ) : Metric.ball G.limit.base r = g.ball G.limit.base r := by
    simpa only [FlowCarrier.metricBall] using
      G.limit.carrier.metricBall_eq_metricBallOf g G.limit.base r
  have hcompactBall (r : ℝ) : IsCompact (closure (g.ball G.limit.base r)) := by
    apply IsCompact.of_isClosed_subset
      (g.isCompact_closedBall_of_metricComplete
        (G.limit.complete 0 G.limit.zero_mem) G.limit.base r) isClosed_closure
    apply closure_minimal
      (fun x (hx : g.edist G.limit.base x < ENNReal.ofReal r) => hx.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  let Yplus : TopologicalSpace.Opens G.limit.carrier.carrier :=
    ⟨g.ball G.limit.base (A + 1), by rw [← hball]; exact Metric.isOpen_ball⟩
  have hYcompact : IsCompact (closure (Y : Set G.limit.carrier.carrier)) := by
    rw [hY]
    exact hcompactBall A
  have hYne : (Y : Set G.limit.carrier.carrier).Nonempty := by
    rw [hY, ← hball]
    exact ⟨G.limit.base, Metric.mem_ball_self hA⟩
  have hbuffer : closure (Y : Set G.limit.carrier.carrier) ⊆ Yplus := by
    change closure (Y : Set G.limit.carrier.carrier) ⊆ g.ball G.limit.base (A + 1)
    rw [hY, ← hball, ← hball]
    exact Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith))
  exact exists_nonnegative_left_extension_on_stage hShi hT G hbranch hcompact hcyl
    Y Yplus hYcompact hYne (hcompactBall (A + 1)) hbuffer




theorem exists_complete_closed_left_extension_of_radius_dependent_cylinders
    (hShi : LocalCurvatureDerivativeEstimates.{u})
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ} (hT : 0 < T)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (hbranch : ∀ k, generalizedPinchedOrNonnegative (S.flow k))
    (hcompact : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (S.baseBall (G.subsequence k) A)))
    (hcyl : ∀ A : ℝ, 0 < A →
      ∃ delta : ℝ, 0 < delta ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (G.subsequence k)
            A (T + delta) B 1)) :
    ∃ Fbar : RicciFlow 3 G.limit.carrier.carrier (Icc (-T) 0),
      (∀ t ∈ Ioc (-T) 0, Fbar.metric t = G.limit.flow.metric t) ∧
      (∀ t ∈ Icc (-T) 0, G.limit.carrier.metricComplete (Fbar.metric t)) ∧
      (∀ t ∈ Icc (-T) 0, ∀ x : G.limit.carrier.carrier,
        (Fbar.connection t).NonnegativeCurvatureOperator x) ∧
      (∀ (x : G.limit.carrier.carrier) (v : TangentSpace (𝓡 3) x),
        (G.limit.flow.metric 0).inner x v v ≤ (Fbar.metric (-T)).inner x v v) ∧
      ∀ A : ℝ, 0 < A →
      ∀ U : TopologicalSpace.Opens G.limit.carrier.carrier,
        (U : Set G.limit.carrier.carrier) =
          (G.limit.flow.metric 0).ball G.limit.base A →
        ∃ delta : ℝ, 0 < delta ∧
          ∃ P : RicciFlow 3 U (Icc (-(T + delta)) 0),
            (∀ t ∈ Icc (-T) 0, ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
              (P.metric t).inner x v w = (Fbar.metric t).inner x.val
                (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.carrier.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.carrier.carrier) x w)) ∧
            ∀ t ∈ Icc (-(T + delta)) 0, ∀ x : U,
              (P.connection t).NonnegativeCurvatureOperator x := by
  exact exists_closed_left_flow_of_local_extensions hT G
    (fun A hA U hU => exists_nonnegative_left_extension_on_terminal_ball
      hShi hT G hbranch hcompact hcyl A hA U hU)

end PoincareConjecture.M30
