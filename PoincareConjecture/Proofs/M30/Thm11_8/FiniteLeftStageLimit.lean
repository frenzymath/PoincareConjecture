import PoincareConjecture.Proofs.M30.Thm11_8.FiniteLeftCoefficients
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.StaticLocalFlowDescent
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.SimultaneousChartFlowLimits
import PoincareConjecture.Proofs.M28.Mathlib.FiniteBufferedChartCover
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetsOfAmbient
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding












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



structure FiniteLeftStageLimit
    {S : GeneralizedBlowupSequence.{u}} {T tau : ℝ}
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (Yplus : TopologicalSpace.Opens G.limit.carrier.carrier)
    (P : ℕ → RicciFlow 3 Yplus (Icc (-tau) 0))
    (K : Set G.limit.carrier.carrier) where
  domain : TopologicalSpace.Opens G.limit.carrier.carrier
  contains : K ⊆ domain
  subset : (domain : Set G.limit.carrier.carrier) ⊆ Yplus
  flow : RicciFlow 3 domain (Icc (-tau) 0)
  interior_metric : ∀ t ∈ Ioc (-T) 0, ∀ (x : domain)
    (v w : TangentSpace (𝓡 3) x),
    (flow.metric t).inner x v w = (G.limit.flow.metric t).inner x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : domain → G.limit.carrier.carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : domain → G.limit.carrier.carrier) x w)
  nonnegative : ∀ t ∈ Icc (-tau) 0, ∀ x : domain,
    (flow.connection t).NonnegativeCurvatureOperator x
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  chartDomain : ℕ → Set (EuclideanSpace ℝ (Fin 3))
  chartDomain_open : ∀ i, IsOpen (chartDomain i)
  chartDomain_nonempty : ∀ i, Nonempty (chartDomain i)
  sourceChart : ∀ i, chartDomain i → Yplus
  sourceChart_localDiffeomorph : ∀ i,
    letI := (chartDomain_open i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sourceChart i)
  coordinateLimit : ∀ i, letI := chartDomain_nonempty i
    M28.FixedCoordinateFlowLimit P (chartDomain i) (chartDomain_open i)
      (fun _ => sourceChart i)
  coordinate_subsequence : ∀ i, (coordinateLimit i).subsequence = subsequence
  limitChart : ∀ i, chartDomain i → domain
  limitChart_localDiffeomorph : ∀ i,
    letI := (chartDomain_open i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (limitChart i)
  chart_cover : ∀ x : domain, ∃ i y, limitChart i y = x
  chart_source : ∀ i x, (sourceChart i x).val = (limitChart i x).val
  chart_metric : ∀ i,
    letI := (chartDomain_open i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (chartDomain_open i).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ t ∈ Icc (-tau) 0, ∀ (x : chartDomain i) (v w : TangentSpace (𝓡 3) x),
      ((coordinateLimit i).flow.metric t).inner x v w =
        (flow.metric t).inner (limitChart i x)
          (mfderiv (𝓡 3) (𝓡 3) (limitChart i) x v)
          (mfderiv (𝓡 3) (𝓡 3) (limitChart i) x w)

private theorem finiteLeft_openCodomain
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

set_option maxHeartbeats 3600000 in



theorem exists_finiteLeftStageLimit
    {S : GeneralizedBlowupSequence.{u}} {T tau : ℝ} (hT : 0 < T)
    (hTtau : T < tau)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (Yplus : TopologicalSpace.Opens G.limit.carrier.carrier) (N : ℕ)
    (P : ℕ → RicciFlow 3 Yplus (Icc (-tau) 0))
    (hstage : ∀ k, (Yplus : Set G.limit.carrier.carrier) ⊆
      G.exhaustion.space (k + N))
    (hmetric : ∀ k s (_hs : s ∈ Icc (-tau) 0)
        (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0)
        (x : Yplus) (v w : TangentSpace (𝓡 3) x),
      ((P k).metric s).inner x v w =
        (G.embedding (k + N)).pullbackInner s hsG x.val
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : Yplus → G.limit.carrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : Yplus → G.limit.carrier.carrier) x w))
    (hcurv : ∀ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ k t,
      t ∈ Icc (-tau) 0 → ∀ x : Yplus,
        ((P k).connection t).curvatureDerivativeNorm m x ≤ D)
    (hdefect : ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Icc (-tau) 0, ∀ x : Yplus,
        ((P k).connection t).negativeCurvaturePart x ≤ eta)
    (K : Set G.limit.carrier.carrier) (hK : IsCompact K) (hKne : K.Nonempty)
    (hKplus : K ⊆ Yplus) :
    Nonempty (FiniteLeftStageLimit G Yplus P K) := by
  classical
  let Euc := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (Euc →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (Euc →L[ℝ] Euc →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have htau : 0 < tau := hT.trans hTtau
  let J := Icc (-tau) 0
  have hzero : (0 : ℝ) ∈ J := ⟨by linarith, le_rfl⟩
  have hIoc : Ioc (-T) 0 ⊆ J := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨q, radius, _, hchart, hcover⟩ :=
    hK.exists_nat_buffered_extChart_ball_cover hKne (𝓡 3) Yplus.isOpen hKplus
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
  let d (i : ℕ) : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.carrier.carrier
      (EuclideanSpace ℝ (Fin 3)) ∞ := {
    toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin 3)) (q i)).toPartialEquiv
    open_source := (chartAt (EuclideanSpace ℝ (Fin 3)) (q i)).open_source
    open_target := (chartAt (EuclideanSpace ℝ (Fin 3)) (q i)).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hdmap (i : ℕ) :
      ((d i).symm : EuclideanSpace ℝ (Fin 3) → G.limit.carrier.carrier) = (c i).symm := by
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
    apply finiteLeft_openCodomain Yplus (eplus i)
    intro x
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (U i) (hU i) ∞ x).comp
      (𝓡 3) G.limit.carrier.carrier (hcinv i (hUtarget i x.property))
  have heambient (i : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun x : V i => (c i).symm x.val) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (V i) (hV i) ∞ x).comp
      (𝓡 3) G.limit.carrier.carrier (hcinv i (hVtarget i x.property))
  have he (i : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e i) :=
    finiteLeft_openCodomain Yplus (e i) (heambient i)
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
      EqOn (((P k).metric t).pullbackCoefficients (param i))
        (((P k).metric t).pullbackCoefficients (psi i)) (V i) := by
    intro x hx
    have hnear : param i =ᶠ[𝓝 x] psi i := by
      filter_upwards [(hV i).mem_nhds hx] with y hy
      exact hmaps i hy
    ext v w
    change ((P k).metric t).inner (param i x)
        (mfderiv (𝓡 3) (𝓡 3) (param i) x v) (mfderiv (𝓡 3) (𝓡 3) (param i) x w) = _
    rw [hnear.self_of_nhds, hnear.mfderiv_eq]
    rfl
  have hdata (i : ℕ) := generalized_stage_coefficients_and_closed_bounds hT hTtau G
    Yplus N P hstage hmetric hcurv (q i) (U i) (hU i) (hUtarget i) (psi i)
      (hpsi i) (hpsival i) (hpsiinv i)
  have hbounds (i : ℕ) := (hdata i).2.2 (C i) (hCcompact i) (hCU i)
  have hell (i : ℕ) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ J, ∀ x ∈ V i, ∀ v,
        alpha * ‖v‖ ^ 2 ≤ ((P k).metric t).pullbackCoefficients (param i) x v v := by
    obtain ⟨alpha, beta, ha, _, hell, _⟩ := hbounds i
    refine ⟨alpha, ha, hell.mono ?_⟩
    intro k hk t ht x hx v
    rw [hcoeff k t i hx]
    exact (hk t ht x (hVC i hx) v).1
  have hjets (i : ℕ) (K' : Set (ℝ × EuclideanSpace ℝ (Fin 3)))
      (_hK' : IsCompact K') (hK'V : K' ⊆ J ×ˢ V i) (m : ℕ) :
      ∃ B : ℝ, ∀ᶠ k : ℕ in atTop, ∀ z ∈ K',
        ‖iteratedFDerivWithin ℝ m
          (fun z => ((P k).metric z.1).pullbackCoefficients (param i) z.2) (J ×ˢ V i) z‖ ≤ B := by
    obtain ⟨_, _, _, _, _, hjet⟩ := hbounds i
    obtain ⟨B, _, hB⟩ := hjet m
    refine ⟨B, hB.mono ?_⟩
    intro k hk z hz
    have heq : EqOn
        (fun z => ((P k).metric z.1).pullbackCoefficients (param i) z.2)
        (fun z => ((P k).metric z.1).pullbackCoefficients (psi i) z.2) (J ×ˢ V i) :=
      fun z hz => hcoeff k z.1 i hz.2
    rw [heq.iteratedFDerivWithin m (hK'V hz),
      ← iteratedFDerivWithin_prod_eq_of_isOpen
        (fun z => ((P k).metric z.1).pullbackCoefficients (psi i) z.2) m
        (hU i) (hV i) (hVU i (hK'V hz).2) (hK'V hz).2]
    exact hk z ⟨(hK'V hz).1, hVC i (hK'V hz).2⟩
  obtain ⟨sigma, hsigma, L, hL, hsign⟩ :=
    exists_simultaneous_nonnegative_coordinateFlowLimits htau P V hV
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
  let O : TopologicalSpace.Opens G.limit.carrier.carrier := ⟨Oset, hOopen⟩
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
    finiteLeft_openCodomain Yplus inc (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) O)
  have hOincl := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) O
  let chartMap (i : ℕ) : V i → O :=
    fun x => ⟨(c i).symm x, mem_iUnion.mpr ⟨i, x.val, x.property, rfl⟩⟩
  have hchartMap (i : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (chartMap i) :=
    finiteLeft_openCodomain O (chartMap i) (heambient i)
  have hcoverO (x : O) : ∃ i y, chartMap i y = x := by
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp x.property
    exact ⟨i, ⟨z, hz⟩, Subtype.ext hzx⟩
  let gO (t : ℝ) := (G.limit.flow.metric t).pullbackOfLocalDiffeomorph
    (Subtype.val : O → G.limit.carrier.carrier) hOincl
  let h (k : ℕ) (t : ℝ) := ((P (sigma k)).metric t).pullbackOfLocalDiffeomorph inc hinc
  have hsourceInner (k : ℕ) (t : ℝ) (i : ℕ) (x : V i) (v w : TangentSpace (𝓡 3) x) :
      (h k t).inner (chartMap i x) (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v)
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w) =
      ((P (sigma k)).metric t).pullbackCoefficients (param i) x v w := by
    have hd := mfderiv_comp x ((hinc (chartMap i x)).mdifferentiableAt (by simp))
      ((hchartMap i x).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (e i) x =
      (mfderiv (𝓡 3) (𝓡 3) inc (chartMap i x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x) at hd
    have hp := mfderiv_chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
      (i := ()) x ((he i).contMDiff x)
    change ((P (sigma k)).metric t).inner (inc (chartMap i x))
        (mfderiv (𝓡 3) (𝓡 3) inc (chartMap i x)
          (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v))
        (mfderiv (𝓡 3) (𝓡 3) inc (chartMap i x)
          (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w)) =
      ((P (sigma k)).metric t).inner (param i x)
        (mfderiv (𝓡 3) (𝓡 3) (param i) x v) (mfderiv (𝓡 3) (𝓡 3) (param i) x w)
    rw [show param i x = e i x from chartParametrization_apply _ _ (i := ()) _ _, hp]
    exact congrArg₂ (fun a b => ((P (sigma k)).metric t).inner (e i x) a b)
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
  have hinteriorO : ∀ t ∈ Ioc (-T) 0, ∀ i (x : V i) (v w : TangentSpace (𝓡 3) x),
      ((L i).flow.metric t).inner x v w = (gO t).inner (chartMap i x)
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v)
        (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w) := by
    intro t ht i x v w
    change Euc at v w
    have hpoint := ((hdata i).2.1 0 {(t, x.val)} isCompact_singleton
      (singleton_subset_iff.mpr ⟨ht, hVU i x.property⟩)).tendsto_at (mem_singleton _)
    have href0 := ((ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin 3))).continuous.tendsto _).comp hpoint
    have href : Tendsto (fun k => ((P k).metric t).pullbackCoefficients (psi i) x.val)
        atTop (𝓝 ((G.limit.flow.metric t).pullbackCoefficients (c i).symm x.val)) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using! href0
    have hrefvw := ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp
        (href.comp hsigma.tendsto_atTop))
    have hl := (L i).metric_inner_tendsto htau (fun _ => he i) t (hIoc ht) x v w
    rw [hL i] at hl
    have hlwide : Tendsto (fun k => ((P (sigma k)).metric t).pullbackCoefficients
        (psi i) x v w) atTop (𝓝 (((L i).flow.metric t).inner x v w)) :=
      hl.congr' (Eventually.of_forall fun k => congrArg (fun Q => Q v w)
        (hcoeff (sigma k) t i x.property))
    apply (tendsto_nhds_unique hlwide hrefvw).trans
    let pO := chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
      (i := ()) (chartMap i)
    have hpO : ContMDiffOn (𝓡 3) (𝓡 3) ∞ pO (V i) :=
      contMDiffOn_chartParametrization (fun _ : Unit => V i) (fun _ => hV i)
        (i := ()) (hchartMap i).contMDiff
    have hnear : (Subtype.val : O → G.limit.carrier.carrier) ∘ pO =ᶠ[𝓝 x.val] (c i).symm := by
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
    change (G.limit.flow.metric t).inner ((c i).symm x.val)
        (mfderiv (𝓡 3) (𝓡 3) (c i).symm x.val v)
        (mfderiv (𝓡 3) (𝓡 3) (c i).symm x.val w) =
      (G.limit.flow.metric t).inner (chartMap i x).val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : O → G.limit.carrier.carrier) (chartMap i x)
          (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x v))
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : O → G.limit.carrier.carrier) (chartMap i x)
          (mfderiv (𝓡 3) (𝓡 3) (chartMap i) x w))
    exact congrArg₂ (fun a b => (G.limit.flow.metric t).inner ((c i).symm x.val) a b)
      (congrArg (fun A => A v) hd) (congrArg (fun A => A w) hd)
  obtain ⟨FO, _, hFOchart, hFOsign⟩ := exists_flow_of_common_metric_chart_limits
    0 hzero (gO 0) h (fun i => (L i).flow) chartMap hchartMap hcoverO hlimit
      (hinteriorO 0 ⟨by linarith, le_rfl⟩) hsign
  have hFOinterior : ∀ t ∈ Ioc (-T) 0, ∀ (x : O) (v w : TangentSpace (𝓡 3) x),
      (FO.metric t).inner x v w = (gO t).inner x v w := by
    intro t ht x v w
    obtain ⟨i, y, rfl⟩ := hcoverO x
    let A := (hchartMap i y).mfderivToContinuousLinearEquiv (by simp)
    obtain ⟨v', hv⟩ := A.surjective v
    obtain ⟨w', hw⟩ := A.surjective w
    change mfderiv (𝓡 3) (𝓡 3) (chartMap i) y v' = v at hv
    change mfderiv (𝓡 3) (𝓡 3) (chartMap i) y w' = w at hw
    rw [← hv, ← hw, ← hFOchart t (hIoc ht) i y v' w']
    exact hinteriorO t ht i y v' w'
  exact ⟨{
    domain := O
    contains := hKO
    subset := hOplus
    flow := FO
    interior_metric := hFOinterior
    nonnegative := hFOsign
    subsequence := sigma
    subsequence_strictMono := hsigma
    chartDomain := V
    chartDomain_open := hV
    chartDomain_nonempty := fun i => inferInstance
    sourceChart := e
    sourceChart_localDiffeomorph := he
    coordinateLimit := L
    coordinate_subsequence := hL
    limitChart := chartMap
    limitChart_localDiffeomorph := hchartMap
    chart_cover := hcoverO
    chart_source := fun _ _ => rfl
    chart_metric := fun i t ht x v w => hFOchart t ht i x v w }⟩



theorem FiniteLeftStageLimit.scalarCurvature_tendsto
    {S : GeneralizedBlowupSequence.{u}} {T tau : ℝ}
    {G : GeneralizedBlowupConvergence S (Ioc (-T) 0)}
    {Yplus : TopologicalSpace.Opens G.limit.carrier.carrier}
    {P : ℕ → RicciFlow 3 Yplus (Icc (-tau) 0)} {K : Set G.limit.carrier.carrier}
    (L : FiniteLeftStageLimit G Yplus P K) (htau : 0 < tau)
    (t : ℝ) (ht : t ∈ Icc (-tau) 0) (x : L.domain) :
    Tendsto (fun k => ((P (L.subsequence k)).connection t).scalarCurvature
      (⟨x.val, L.subset x.property⟩ : Yplus)) atTop
        (𝓝 ((L.flow.connection t).scalarCurvature x)) := by
  obtain ⟨i, y, rfl⟩ := L.chart_cover x
  let := L.chartDomain_nonempty i
  let := (L.chartDomain_open i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (L.chartDomain_open i).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  have h := (L.coordinateLimit i).scalarCurvature_tendsto htau
    (fun _ => L.sourceChart_localDiffeomorph i) t ht y
  have heq := ((L.coordinateLimit i).flow.connection t).scalarCurvature_eq_of_local_isometry
    (L.flow.connection t) isOpen_univ
    (L.limitChart_localDiffeomorph i).contMDiff.contMDiffOn
    (fun z _ v w => L.chart_metric i t ht z v w) (mem_univ y)
  rw [L.coordinate_subsequence i, heq] at h
  exact h.congr' (Eventually.of_forall fun _ =>
    congrArg (fun z => ((P _).connection t).scalarCurvature z)
      (Subtype.ext (L.chart_source i y)))

end PoincareConjecture.M30
