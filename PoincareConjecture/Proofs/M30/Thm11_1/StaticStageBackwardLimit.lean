import PoincareConjecture.Proofs.M30.Thm11_1.StaticStageSourceFlows
import PoincareConjecture.Proofs.M30.Thm5_33.RetainedSourceDefect
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.StaticLocalFlowDescent
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.StaticStageCoordinateBounds
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.SimultaneousChartFlowLimits
import PoincareConjecture.Proofs.M28.Mathlib.FiniteBufferedChartCover
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetsOfAmbient
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric PoincareConjecture.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem staticStage_openCodomain
    {X : Type v} {Z : Type w} [TopologicalSpace X] [TopologicalSpace Z]
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

set_option maxHeartbeats 2400000 in





theorem exists_nonnegative_backward_flow_on_static_stage
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r0 mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r0 mu)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (G : PartialPointedMetricConvergence
      (terminalComponentMetric S) (terminalComponentBase S) 1)
    (hcomplete : G.limitCarrier.metricComplete G.limitMetric) (j : ℕ) :
    let Y : TopologicalSpace.Opens G.limitCarrier.carrier :=
      ⟨G.exhaustion j, G.exhaustion_open j⟩
    let g0 : RiemannianMetric 3 Y :=
      G.limitMetric.pullbackOfLocalDiffeomorph
        (Subtype.val : Y → G.limitCarrier.carrier)
        (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y)
    ∃ tau : ℝ, 0 < tau ∧ ∃ F : RicciFlow 3 Y (Icc (-tau) 0),
      F.metric 0 = g0 ∧ ∀ t ∈ Icc (-tau) 0, ∀ x : Y,
        (F.connection t).NonnegativeCurvatureOperator x := by
  classical
  intro Y g0
  let Euc := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (Euc →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (Euc →L[ℝ] Euc →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let Yplus : TopologicalSpace.Opens G.limitCarrier.carrier :=
    ⟨G.exhaustion (j + 1), G.exhaustion_open (j + 1)⟩
  obtain ⟨W, T, B, _hW, hT, hB, N, E, P, himage, hP, hterminal, hcurv⟩ :=
    exists_source_flows_on_static_stage hC H hbound G hcomplete (j + 1)
  let tau := T / 2
  have htau : 0 < tau := half_pos hT
  let J := Icc (-tau) 0
  have hzero : (0 : ℝ) ∈ J := ⟨by linarith, le_rfl⟩
  have hJsub : J ⊆ Icc (-T) 0 := by
    intro t ht
    have hleft : -(T / 2) ≤ t := ht.1
    exact ⟨by linarith, ht.2⟩
  have hJne : J.Nontrivial :=
    ⟨-tau, ⟨le_rfl, by linarith⟩, 0, hzero, by linarith⟩
  let P0 (k : ℕ) : RicciFlow 3 Yplus J :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow (P k) hJsub ordConnected_Icc hJne
  have hcurv0 (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ k t, t ∈ J → ∀ x : Yplus,
      ((P0 k).connection t).curvatureDerivativeNorm m x ≤ D := by
    obtain ⟨D, hD, hDall⟩ := hcurv m
    exact ⟨D, hD.le, hDall⟩
  let phi (k : ℕ) := G.subsequence (k + N)
  have hphi : StrictMono phi :=
    G.subsequence_strictMono.comp (fun _ _ h => Nat.add_lt_add_right h N)
  let f (k : ℕ) : Yplus → ((S.flow (phi k)).slice (S.base (phi k)).1).carrier :=
    fun x => (G.embedding (k + N) x.val).val
  have hf : ∀ᶠ k : ℕ in atTop, ContMDiff (𝓡 3) (𝓡 3) ∞ (f k) := by
    filter_upwards [eventually_ge_atTop (j + 1)] with k hk
    let fc : Yplus → (terminalComponentCarrier S (phi k)).carrier :=
      fun x => G.embedding (k + N) x.val
    have hfc : ContMDiff (𝓡 3) (𝓡 3) ∞ fc := by
      intro x
      exact ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Yplus x).comp (𝓡 3)
        (terminalComponentCarrier S (phi k)).carrier
        (G.embedding_smooth (k + N)
          ⟨x.val, G.exhaustion_monotone (by omega) x.property⟩)).contMDiffAt
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3)
      (Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3))
        (S.base (phi k)).2)).contMDiff.comp hfc
  have hdefect (eta : ℝ) (heta : 0 < eta) : ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ J, ∀ x : Yplus, ((P0 k).connection t).negativeCurvaturePart x ≤ eta := by
    have h := eventually_retained_source_negativeDefect_le S H.branch phi hphi hT hB
      E f hf himage P hP eta heta
    exact h.mono fun k hk t ht x => hk t (hJsub ht) x

  let K := closure (G.exhaustion j)
  obtain ⟨q, radius, _, hchart, hcover⟩ :=
    (G.exhaustion_compactClosure j).exists_nat_buffered_extChart_ball_cover
      ⟨G.base, subset_closure (G.base_in_exhaustion j)⟩ (𝓡 3)
      (G.exhaustion_open (j + 1)) (G.exhaustion_step j)
  let c (i : ℕ) := extChartAt (𝓡 3) (q i)
  let U (i : ℕ) := ball (c i (q i)) (2 * radius i)
  let C (i : ℕ) := closedBall (c i (q i)) (radius i)
  let V (i : ℕ) := ball (c i (q i)) (radius i)
  have hr (i : ℕ) : 0 < radius i := (hchart i).2.1
  have hU (i : ℕ) : IsOpen (U i) := isOpen_ball
  have hV (i : ℕ) : IsOpen (V i) := isOpen_ball
  have hCcompact (i : ℕ) : IsCompact (C i) := isCompact_closedBall _ _
  have hVC (i : ℕ) : V i ⊆ C i := ball_subset_closedBall
  have hCU (i : ℕ) : C i ⊆ U i := by
    intro x hx
    change dist x (c i (q i)) ≤ radius i at hx
    change dist x (c i (q i)) < 2 * radius i
    linarith [hr i]
  have hVU (i : ℕ) : V i ⊆ U i := (hVC i).trans (hCU i)
  have hUtarget (i : ℕ) : U i ⊆ (c i).target :=
    fun _ hx => ((hchart i).2.2 (ball_subset_closedBall hx)).1
  have hUimage (i : ℕ) : ∀ x ∈ U i, (c i).symm x ∈ Yplus :=
    fun _ hx => ((hchart i).2.2 (ball_subset_closedBall hx)).2
  have hVtarget (i : ℕ) : V i ⊆ (c i).target := (hVU i).trans (hUtarget i)
  let : ∀ i, Nonempty (U i) := fun i =>
    ⟨⟨c i (q i), mem_ball_self (mul_pos (by norm_num) (hr i))⟩⟩
  let : ∀ i, Nonempty (V i) := fun i => ⟨⟨c i (q i), mem_ball_self (hr i)⟩⟩
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (V i) :=
    fun i => (hV i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (V i) :=
    fun i => (hV i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let d (i : ℕ) : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limitCarrier.carrier
      (EuclideanSpace ℝ (Fin 3)) ∞ := {
    toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin 3)) (q i)).toPartialEquiv
    open_source := (chartAt (EuclideanSpace ℝ (Fin 3)) (q i)).open_source
    open_target := (chartAt (EuclideanSpace ℝ (Fin 3)) (q i)).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hdmap (i : ℕ) :
      ((d i).symm : EuclideanSpace ℝ (Fin 3) → G.limitCarrier.carrier) = (c i).symm := by
    dsimp only [c]
    rw [extChartAt_coe_symm]
    rfl
  have hdtarget (i : ℕ) : (d i).target = (c i).target := by
    simp only [c, extChartAt_target, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ]
    rfl
  have hcinv (i : ℕ) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (c i).target) :
      IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (c i).symm x := by
    refine ⟨(d i).symm, ?_, ?_⟩
    · change x ∈ (d i).target
      rwa [hdtarget]
    · intro y _
      exact congrFun (hdmap i).symm y
  let eplus (i : ℕ) : U i → Yplus := fun x => ⟨(c i).symm x, hUimage i x x.property⟩
  let e (i : ℕ) : V i → Yplus :=
    fun x => ⟨(c i).symm x, hUimage i x (hVU i x.property)⟩
  have heplus (i : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (eplus i) := by
    apply staticStage_openCodomain Yplus (eplus i)
    intro x
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (U i) (hU i) ∞ x).comp
      (𝓡 3) G.limitCarrier.carrier (hcinv i (hUtarget i x.property))
  have heambient (i : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun x : V i => (c i).symm x.val) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (V i) (hV i) ∞ x).comp
      (𝓡 3) G.limitCarrier.carrier (hcinv i (hVtarget i x.property))
  have he (i : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e i) :=
    staticStage_openCodomain Yplus (e i) (heambient i)
  let psi (i : ℕ) := chartParametrization (fun _ : Unit => U i) (fun _ => hU i)
    (i := ()) (eplus i)
  let param (i : ℕ) := chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
    (i := ()) (e i)
  have hpsi (i : ℕ) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (psi i) (U i) :=
    contMDiffOn_chartParametrization (fun _ : Unit => U i) (fun _ => hU i)
      (i := ()) (heplus i).contMDiff
  have hpsival (i : ℕ) : ∀ x ∈ U i, (psi i x).val = (c i).symm x := by
    intro x hx
    change (psi i (⟨x, hx⟩ : U i)).val = _
    rw [show psi i (⟨x, hx⟩ : U i) = eplus i ⟨x, hx⟩ from
      chartParametrization_apply _ _ (i := ()) _ _]
  have hpsiinv (i : ℕ) : ∀ x ∈ U i, (mfderiv (𝓡 3) (𝓡 3) (psi i) x).IsInvertible := by
    intro x hx
    have hd := mfderiv_chartParametrization (fun _ : Unit => U i) (fun _ => hU i)
      (i := ()) (⟨x, hx⟩ : U i) ((heplus i).contMDiff ⟨x, hx⟩)
    rw [hd]
    exact ⟨(heplus i ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hmaps (i : ℕ) : EqOn (param i) (psi i) (V i) := by
    intro x hx
    calc
      param i x = e i ⟨x, hx⟩ := chartParametrization_apply
        (fun _ : Unit => V i) (fun _ => hV i) (i := ()) (e i) (⟨x, hx⟩ : V i)
      _ = eplus i ⟨x, hVU i hx⟩ := rfl
      _ = psi i x := (chartParametrization_apply
        (fun _ : Unit => U i) (fun _ => hU i) (i := ()) (eplus i)
          (⟨x, hVU i hx⟩ : U i)).symm
  have hcoeff (k : ℕ) (t : ℝ) (i : ℕ) :
      EqOn (((P0 k).metric t).pullbackCoefficients (param i))
        (((P0 k).metric t).pullbackCoefficients (psi i)) (V i) := by
    intro x hx
    have hnear : param i =ᶠ[𝓝 x] psi i := by
      filter_upwards [(hV i).mem_nhds hx] with y hy
      exact hmaps i hy
    ext v w
    change ((P0 k).metric t).inner (param i x)
        (mfderiv (𝓡 3) (𝓡 3) (param i) x v) (mfderiv (𝓡 3) (𝓡 3) (param i) x w) = _
    rw [hnear.self_of_nhds, hnear.mfderiv_eq]
    rfl
  have hbounds (i : ℕ) := G.exists_static_stage_coordinate_bounds (j + 1) N htau
    P0 hterminal hcurv0 (q i) (U i) (hU i) (hUtarget i) (psi i)
      (hpsi i) (hpsival i) (hpsiinv i) (C i) (hCcompact i) (hCU i)
  have hell (i : ℕ) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ J, ∀ x ∈ V i, ∀ v,
        alpha * ‖v‖ ^ 2 ≤ ((P0 k).metric t).pullbackCoefficients (param i) x v v := by
    obtain ⟨alpha, beta, ha, _, hell, _⟩ := hbounds i
    refine ⟨alpha, ha, hell.mono ?_⟩
    intro k hk t ht x hx v
    rw [hcoeff k t i hx]
    exact (hk t ht x (hVC i hx) v).1
  have hjets (i : ℕ) (K' : Set (ℝ × EuclideanSpace ℝ (Fin 3)))
      (_hK' : IsCompact K') (hK'V : K' ⊆ J ×ˢ V i) (m : ℕ) :
      ∃ B : ℝ, ∀ᶠ k : ℕ in atTop, ∀ z ∈ K',
        ‖iteratedFDerivWithin ℝ m
          (fun z => ((P0 k).metric z.1).pullbackCoefficients (param i) z.2) (J ×ˢ V i) z‖ ≤ B := by
    obtain ⟨_, _, _, _, _, hjet⟩ := hbounds i
    obtain ⟨B, _, hB⟩ := hjet m
    refine ⟨B, hB.mono ?_⟩
    intro k hk z hz
    have heq : EqOn
        (fun z => ((P0 k).metric z.1).pullbackCoefficients (param i) z.2)
        (fun z => ((P0 k).metric z.1).pullbackCoefficients (psi i) z.2) (J ×ˢ V i) :=
      fun z hz => hcoeff k z.1 i hz.2
    rw [heq.iteratedFDerivWithin m (hK'V hz),
      ← iteratedFDerivWithin_prod_eq_of_isOpen
        (fun z => ((P0 k).metric z.1).pullbackCoefficients (psi i) z.2) m
        (hU i) (hV i) (hVU i (hK'V hz).2) (hK'V hz).2]
    exact hk z ⟨(hK'V hz).1, hVC i (hK'V hz).2⟩
  obtain ⟨sigma, hsigma, L, hL, hsign⟩ :=
    exists_simultaneous_nonnegative_coordinateFlowLimits htau P0 V hV
      (fun i => convex_ball _ _) (fun i _ => e i) (fun i _ => he i) hell hjets hdefect

  let Oset := ⋃ i, (c i).symm '' V i
  have hOopen : IsOpen Oset := by
    apply isOpen_iUnion
    intro i
    rw [← hdmap i]
    apply (d i).toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target (hV i)
    change V i ⊆ (d i).target
    rw [hdtarget]
    exact hVtarget i
  let O : TopologicalSpace.Opens G.limitCarrier.carrier := ⟨Oset, hOopen⟩
  have hKO : K ⊆ Oset := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i, c i x, hi.2, (c i).left_inv hi.1⟩
  have hOplus : Oset ⊆ Yplus := by
    intro x hx
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hx
    exact hUimage i z (hVU i hz)
  let inc : O → Yplus := fun x => ⟨x.val, hOplus x.property⟩
  have hinc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ inc :=
    staticStage_openCodomain Yplus inc (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) O)
  have hOincl := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) O
  let chartMap (i : ℕ) : V i → O :=
    fun x => ⟨(c i).symm x, mem_iUnion.mpr ⟨i, x.val, x.property, rfl⟩⟩
  have hchartMap (i : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (chartMap i) :=
    staticStage_openCodomain O (chartMap i) (heambient i)
  have hcoverO (x : O) : ∃ i y, chartMap i y = x := by
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp x.property
    exact ⟨i, ⟨z, hz⟩, Subtype.ext hzx⟩
  let gO := G.limitMetric.pullbackOfLocalDiffeomorph
    (Subtype.val : O → G.limitCarrier.carrier) hOincl
  let h (k : ℕ) (t : ℝ) := ((P0 (sigma k)).metric t).pullbackOfLocalDiffeomorph inc hinc
  have hsourceInner (k : ℕ) (t : ℝ) (i : ℕ) (x : V i) (v w : TangentSpace (𝓡 3) x) :
      (h k t).inner (chartMap i x) (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v)
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w) =
      ((P0 (sigma k)).metric t).pullbackCoefficients (param i) x v w := by
    have hd := mfderiv_comp x ((hinc (chartMap i x)).mdifferentiableAt (by simp))
      ((hchartMap i x).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (e i) x =
      (mfderiv (𝓡 3) (𝓡 3) inc (chartMap i x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x) at hd
    have hp := mfderiv_chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
      (i := ()) x ((he i).contMDiff x)
    change ((P0 (sigma k)).metric t).inner (inc (chartMap i x))
        (mfderiv (𝓡 3) (𝓡 3) inc (chartMap i x)
          (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v))
        (mfderiv (𝓡 3) (𝓡 3) inc (chartMap i x)
          (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w)) =
      ((P0 (sigma k)).metric t).inner (param i x)
        (mfderiv (𝓡 3) (𝓡 3) (param i) x v) (mfderiv (𝓡 3) (𝓡 3) (param i) x w)
    rw [show param i x = e i x from chartParametrization_apply _ _ (i := ()) _ _, hp]
    exact congrArg₂ (fun a b => ((P0 (sigma k)).metric t).inner (e i x) a b)
      (congrArg (fun A => A v) hd).symm (congrArg (fun A => A w) hd).symm
  have hlimit : ∀ t ∈ J, ∀ i (x : V i) (v w : TangentSpace (𝓡 3) x),
      Tendsto (fun k => (h k t).inner (chartMap i x)
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v)
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w)) atTop
          (𝓝 (((L i).flow.metric t).inner x v w)) := by
    intro t ht i x v w
    have hl := (L i).metric_inner_tendsto htau (fun _ => he i) t ht x v w
    rw [hL i] at hl
    exact hl.congr' (Eventually.of_forall fun k => (hsourceInner k t i x v w).symm)
  have hstatic (i : ℕ) : TendstoUniformlyOn
      (fun k => ((P0 k).metric 0).pullbackCoefficients (psi i))
      (G.limitMetric.pullbackCoefficients (c i).symm) atTop (C i) := by
    have hjet := G.tendstoUniformlyOn_static_stage_metric_jets (j + 1) N
      (fun k => (P0 k).metric 0) hterminal (q i) (U i) (hU i) (hUtarget i)
      (psi i) (hpsi i) (hpsival i) 0 (C i) (hCcompact i) (hCU i)
    have hcoeff := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn hjet
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using! hcoeff
  have hterminalO : ∀ i (x : V i) (v w : TangentSpace (𝓡 3) x),
      ((L i).flow.metric 0).inner x v w = gO.inner (chartMap i x)
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v)
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w) := by
    intro i x v w
    change Euc at v w
    have href := ((hstatic i).tendsto_at (hVC i x.property)).comp hsigma.tendsto_atTop
    have hrefvw := ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp href)
    have hl := (L i).metric_inner_tendsto htau (fun _ => he i) 0 hzero x v w
    rw [hL i] at hl
    have hlwide : Tendsto (fun k => ((P0 (sigma k)).metric 0).pullbackCoefficients
        (psi i) x v w) atTop (𝓝 (((L i).flow.metric 0).inner x v w)) :=
      hl.congr' (Eventually.of_forall fun k => congrArg (fun Q => Q v w)
        (hcoeff (sigma k) 0 i x.property))
    have hid := tendsto_nhds_unique hlwide hrefvw
    apply hid.trans
    let pO := chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
      (i := ()) (chartMap i)
    have hpO : ContMDiffOn (𝓡 3) (𝓡 3) ∞ pO (V i) :=
      contMDiffOn_chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
        (i := ()) (hchartMap i).contMDiff
    have hnear : (Subtype.val : O → G.limitCarrier.carrier) ∘ pO =ᶠ[𝓝 x.val] (c i).symm := by
      filter_upwards [(hV i).mem_nhds x.property] with y hy
      change (pO (⟨y, hy⟩ : V i)).val = _
      rw [show pO (⟨y, hy⟩ : V i) = chartMap i ⟨y, hy⟩ from
        chartParametrization_apply _ _ (i := ()) _ _]
    have hd := mfderiv_comp x.val ((hOincl (pO x.val)).mdifferentiableAt (by simp))
      (((hpO x.val x.property).contMDiffAt ((hV i).mem_nhds x.property)).mdifferentiableAt
        (by simp))
    have hp := mfderiv_chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
      (i := ()) x ((hchartMap i).contMDiff x)
    rw [hnear.mfderiv_eq, show pO x.val = chartMap i x from
      chartParametrization_apply _ _ (i := ()) _ _, hp] at hd
    change G.limitMetric.inner ((c i).symm x.val)
        (mfderiv (𝓡 3) (𝓡 3) (c i).symm x.val v)
        (mfderiv (𝓡 3) (𝓡 3) (c i).symm x.val w) =
      G.limitMetric.inner (chartMap i x).val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : O → G.limitCarrier.carrier) (chartMap i x)
          (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v))
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : O → G.limitCarrier.carrier) (chartMap i x)
          (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w))
    exact congrArg₂ (fun a b => G.limitMetric.inner ((c i).symm x.val) a b)
      (congrArg (fun A => A v) hd) (congrArg (fun A => A w) hd)
  obtain ⟨FO, hFOzero, _, hFOsign⟩ := exists_flow_of_common_metric_chart_limits
    0 hzero gO h (fun i => (L i).flow) chartMap hchartMap hcoverO hlimit hterminalO hsign
  let incY : Y → O := fun x => ⟨x.val, hKO (subset_closure x.property)⟩
  have hincY : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ incY :=
    staticStage_openCodomain O incY (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y)
  let F : RicciFlow 3 Y J := FO.pullbackWithConnection incY hincY
    (fun t => ((FO.metric t).pullbackOfLocalDiffeomorph incY hincY).leviCivitaData)
  have hFinner : (F.metric 0).inner = g0.inner := by
    funext x
    ext v w
    change (FO.metric 0).inner (incY x)
        (mfderiv (𝓡 3) (𝓡 3) incY x v) (mfderiv (𝓡 3) (𝓡 3) incY x w) = _
    rw [hFOzero]
    have hd := mfderiv_comp x ((hOincl (incY x)).mdifferentiableAt (by simp))
      ((hincY x).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Y → G.limitCarrier.carrier) x =
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : O → G.limitCarrier.carrier) (incY x)).comp
        (mfderiv (𝓡 3) (𝓡 3) incY x) at hd
    exact congrArg₂ (fun a b => G.limitMetric.inner x.val a b)
      (congrArg (fun A => A v) hd).symm (congrArg (fun A => A w) hd).symm
  have hmetric_ext (g1 g2 : RiemannianMetric 3 Y) (hi : g1.inner = g2.inner) : g1 = g2 := by
    cases g1
    cases g2
    cases hi
    rfl
  refine ⟨tau, htau, F, hmetric_ext _ _ hFinner, ?_⟩
  intro t ht x
  exact ((F.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
    (FO.connection t) isOpen_univ hincY.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)).mpr (hFOsign t ht (incY x))

end PoincareConjecture.M30
