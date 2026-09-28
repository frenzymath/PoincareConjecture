import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.ParametrizedJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.ChangingCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Calculus

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalMovingCylinderCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}
  (hconv : M23TerminalMetricConvergence G e)
  (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
    s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
      ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)
  {J : Set ℝ} (hJ : IsCompact J) (hJzero : J ⊆ Iic 0)
  (τ : ℕ → ℝ) (hτ : ∀ k, τ k ∈ J)

include hconv hfixed hJ hJzero hτ

theorem smooth_zero_convergence_movingTime_changing_parametrized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (eDim : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3))
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → G.limit.carrier.carrier}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 3) ∞ f U)
    {c : ℕ → E → E}
    (hclocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (c k) W)
    (hcbound : ∀ K, IsCompact K → K ⊆ V → ∀ m, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (c k) x‖ ≤ C)
    (hctarget : ∀ K, IsCompact K → K ⊆ V → ∃ T,
      IsCompact T ∧ T ⊆ U ∧ ∀ᶠ k in atTop, MapsTo (c k) K T) :
    let A : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun k x =>
      ((S.term (G.subsequence k)).flow.flow.metric (τ k)).parametrizedCoefficients
        (fun y => ((e k).toFun (0, f (c k y))).2) x -
      (G.limit.flow.flow.metric (τ k)).parametrizedCoefficients (f ∘ c k) x
    (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (fun _ => 0) atTop K := by
  let F : (k : ℕ) → E → (S.term (G.subsequence k)).carrier.carrier :=
    fun k y => ((e k).toFun (0, f y)).2
  let B := fun k =>
    ((S.term (G.subsequence k)).flow.flow.metric (τ k)).parametrizedCoefficients (F k)
  let B₀ := fun k => (G.limit.flow.flow.metric (τ k)).parametrizedCoefficients f
  let D := fun k y => ((B k (c k y)) - B₀ k (c k y)).bilinearComp
    (fderiv ℝ (c k) y) (fderiv ℝ (c k) y)
  let A := fun k x =>
    ((S.term (G.subsequence k)).flow.flow.metric (τ k)).parametrizedCoefficients (F k ∘ c k) x -
      (G.limit.flow.flow.metric (τ k)).parametrizedCoefficients (f ∘ c k) x
  obtain ⟨herrorlocal, herrorjet⟩ := hconv.smooth_zero_convergence_movingTime_parametrized
    hfixed hJ hJzero τ hτ eDim hU hf
  obtain ⟨hDlocal, hDjet⟩ := smooth_zero_convergence_pullback_of_bounded hV
    herrorlocal hclocal herrorjet hcbound hctarget
  have hnear (K : Set E) (hK : IsCompact K) (hKV : K ⊆ V) :
      ∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ᶠ k in atTop, EqOn (D k) (A k) W := by
    obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
    obtain ⟨T, hT, hTU, hmap⟩ := hctarget K' hK' hK'V
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
      (hT.image_of_continuousOn (hf.continuousOn.mono hTU))
    refine ⟨interior K', isOpen_interior, hKK', ?_⟩
    filter_upwards [hmap, eventually_ge_atTop j,
      eventually_contDiffAt_on_compact hK' hK'V hclocal] with k hkmap hkj hkc x hx
    have hxT := hkmap (interior_subset hx)
    have hfx := hf.contMDiffAt (hU.mem_nhds (hTU hxT))
    have hF : MDifferentiableAt 𝓘(ℝ, E) (𝓡 3) (F k) (c k x) :=
      (((e k).terminalSpatialMap_contMDiffAt (G.exhaustion_open k) (t := 0) le_rfl
        (G.exhaustion_monotone hkj (hj (mem_image_of_mem f hxT)))).comp
          (c k x) hfx).mdifferentiableAt (by simp)
    have hc := (hkc x (interior_subset hx)).differentiableAt (by simp)
    change ((B k (c k x)) - B₀ k (c k x)).bilinearComp
      (fderiv ℝ (c k) x) (fderiv ℝ (c k) x) = A k x
    have hsub : ((B k (c k x)) - B₀ k (c k x)).bilinearComp
        (fderiv ℝ (c k) x) (fderiv ℝ (c k) x) =
        (B k (c k x)).bilinearComp (fderiv ℝ (c k) x) (fderiv ℝ (c k) x) -
        (B₀ k (c k x)).bilinearComp (fderiv ℝ (c k) x) (fderiv ℝ (c k) x) := by
      ext v w
      rfl
    rw [hsub]
    exact congrArg₂ (fun v w => v - w)
      (((S.term (G.subsequence k)).flow.flow.metric (τ k)).parametrizedCoefficients_comp_of_eventuallyEq
        hF hc Filter.EventuallyEq.rfl)
      ((G.limit.flow.flow.metric (τ k)).parametrizedCoefficients_comp_of_eventuallyEq
        (hfx.mdifferentiableAt (by simp)) hc Filter.EventuallyEq.rfl)
  change (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, _, hs⟩ := hDlocal x hx
    obtain ⟨W', hW', hxW', heq⟩ := hnear {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    refine ⟨W ∩ W', hW.inter hW', ⟨hxW, hxW' (mem_singleton x)⟩, ?_⟩
    filter_upwards [hs, heq] with k hks hkeq
    exact (hks.mono inter_subset_left).congr (fun y hy => (hkeq hy.2).symm)
  · intro m K hK hKV
    obtain ⟨W, hW, hKW, heq⟩ := hnear K hK hKV
    apply (hDjet m K hK hKV).congr
    filter_upwards [heq] with k hk x hx
    exact (eqOn_iteratedFDeriv_of_isOpen hW hk m) (hKW hx)

theorem smooth_zero_convergence_movingTime_cylinder_parametrizations
    {δ : ℝ} {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹))
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2) :
    let U : Set RoundCylinderCoordinates :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ Ioo (-δ⁻¹) δ⁻¹
    let F : ℕ → RoundCylinderCoordinates → G.limit.carrier.carrier :=
      fun i x => Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
    let A := fun i x =>
      ((S.term (G.subsequence i)).flow.flow.metric (τ i)).parametrizedCoefficients
        (fun y => ((e i).toFun (0, F i y)).2) x -
      (G.limit.flow.flow.metric (τ i)).parametrizedCoefficients (F i) x
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (A i)) (fun _ => 0) atTop K := by
  let U : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 3 ×ˢ Ioo (-δ⁻¹) δ⁻¹
  let V : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ Ioo (-δ⁻¹) δ⁻¹
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
  have hV : IsOpen V := Metric.isOpen_ball.prod isOpen_Ioo
  let f := fun x : RoundCylinderCoordinates =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm x.1, x.2)
  let F := fun i (x : RoundCylinderCoordinates) =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
  let c := fun i => roundCylinderCoordinateTransition p (q i)
  let A := fun i x =>
    ((S.term (G.subsequence i)).flow.flow.metric (τ i)).parametrizedCoefficients
      (fun y => ((e i).toFun (0, F i y)).2) x -
    (G.limit.flow.flow.metric (τ i)).parametrizedCoefficients (F i) x
  let D := fun i x =>
    ((S.term (G.subsequence i)).flow.flow.metric (τ i)).parametrizedCoefficients
      (fun y => ((e i).toFun (0, f (c i y))).2) x -
    (G.limit.flow.flow.metric (τ i)).parametrizedCoefficients (f ∘ c i) x
  let eDim : RoundCylinderCoordinates ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hf : ContMDiffOn 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ f U :=
    hΦ.comp (cylinderChart_symm_smooth p).contMDiffOn (fun x hx => ⟨mem_univ _, hx.2⟩)
  obtain ⟨hDlocal, hDjet⟩ := hconv.smooth_zero_convergence_movingTime_changing_parametrized
    hfixed hJ hJzero τ hτ eDim hU hV hf
    (fun x hx => ⟨V, hV, hx, Eventually.of_forall fun i =>
      (contDiffOn_roundCylinderCoordinateTransition p (q i) (hpq i)).mono
        (prod_mono subset_rfl (subset_univ _))⟩)
    (fun K hK hKV m => by
      obtain ⟨C, _, hC⟩ := exists_uniform_roundCylinderCoordinateTransition_jet_bound
        p q hpq hK (fun x hx => ⟨(hKV hx).1, mem_univ _⟩) m
      exact ⟨C, Eventually.of_forall hC⟩)
    (fun K hK hKV => by
      refine ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2 ×ˢ (Prod.snd '' K),
        (isCompact_closedBall _ _).prod (hK.image continuous_snd), ?_, ?_⟩
      · intro x hx
        refine ⟨Metric.mem_ball.mpr
          ((Metric.mem_closedBall.mp hx.1).trans_lt (by norm_num)), ?_⟩
        rcases hx.2 with ⟨y, hy, hyx⟩
        exact hyx ▸ (hKV hy).2
      · apply Eventually.of_forall
        intro i x hx
        constructor
        · simpa only [Metric.mem_closedBall, dist_zero_right] using
            norm_roundCylinderCoordinateTransition_fst_le_two p (q i) (hpq i)
              (show x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ
                from ⟨(hKV hx).1, mem_univ _⟩)
        · change x.2 ∈ Prod.snd '' K
          exact mem_image_of_mem Prod.snd hx)
  have heq (i : ℕ) : EqOn (D i) (A i) V := by
    intro x hx
    have hpair := roundCylinderCoordinateTransition_chart_inverse_eventuallyEq
      p (q i) (hpq i) ⟨hx.1, mem_univ _⟩
    have hf : (f ∘ c i) =ᶠ[𝓝 x] F i := hpair.fun_comp Φ
    have hsource : (fun y => ((e i).toFun (0, f (c i y))).2) =ᶠ[𝓝 x]
        (fun y => ((e i).toFun (0, F i y)).2) :=
      hf.fun_comp (fun z => ((e i).toFun (0, z)).2)
    exact congrArg₂ (fun v w => v - w)
      (((S.term (G.subsequence i)).flow.flow.metric (τ i)).parametrizedCoefficients_congr_of_eventuallyEq
        hsource)
      ((G.limit.flow.flow.metric (τ i)).parametrizedCoefficients_congr_of_eventuallyEq hf)
  change (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, hs⟩ := hDlocal x hx
    refine ⟨V ∩ W, hV.inter hW, ⟨hx, hxW⟩, ?_⟩
    exact hs.mono fun i hi => (hi.mono inter_subset_right).congr
      (fun y hy => (heq i hy.1).symm)
  · intro m K hK hKV
    exact (hDjet m K hK hKV).congr (Eventually.of_forall fun i x hx =>
      (eqOn_iteratedFDeriv_of_isOpen hV (heq i) m) (hKV hx))

theorem smooth_zero_convergence_movingTime_cylinder_coefficients
    {δ : ℝ} {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹))
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    (v w : Fin 3) :
    let U : Set RoundCylinderCoordinates :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ Ioo (-δ⁻¹) δ⁻¹
    let B := fun i => roundCylinderPullback ((S.term (G.subsequence i)).flow.flow.metric (τ i))
      (fun z => ((e i).toFun (0, Φ z)).2)
    let B₀ := fun i => roundCylinderPullback (G.limit.flow.flow.metric (τ i)) Φ
    let A := fun i x =>
      roundCylinderTensorCoefficient (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
      roundCylinderTensorCoefficient (B₀ i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (A i)) (fun _ => 0) atTop K := by
  let U : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ Ioo (-δ⁻¹) δ⁻¹
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
  have hstrip : IsOpen (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ : Set RoundCylinderSpace) :=
    isOpen_univ.prod isOpen_Ioo
  let f := fun i (z : RoundCylinderSpace) => ((e i).toFun (0, Φ z)).2
  let F := fun i (x : RoundCylinderCoordinates) =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
  let E := fun i x =>
    ((S.term (G.subsequence i)).flow.flow.metric (τ i)).parametrizedCoefficients
      (fun y => ((e i).toFun (0, F i y)).2) x -
    (G.limit.flow.flow.metric (τ i)).parametrizedCoefficients (F i) x
  let B := fun i => roundCylinderPullback ((S.term (G.subsequence i)).flow.flow.metric (τ i)) (f i)
  let B₀ := fun i => roundCylinderPullback (G.limit.flow.flow.metric (τ i)) Φ
  let A := fun i x =>
    roundCylinderTensorCoefficient (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
    roundCylinderTensorCoefficient (B₀ i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
  let L := (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis w)).comp
    (ContinuousLinearMap.apply ℝ (RoundCylinderCoordinates →L[ℝ] ℝ)
      (roundCylinderCoordinateBasis v))
  obtain ⟨hElocal, hEjet⟩ := hconv.smooth_zero_convergence_movingTime_cylinder_parametrizations
    hfixed hJ hJzero τ hτ hΦ p q hpq
  obtain ⟨hDlocal, hDjet⟩ := smooth_convergence_continuousLinearMap_comp L hU
    (contDiffOn_const (c := (0 : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ)))
    hElocal (fun m K hK hKU =>
      (hEjet m K hK hKU).congr_right (fun _ _ => by simp))
  have hnear (K : Set RoundCylinderCoordinates) (hK : IsCompact K) (hKU : K ⊆ U) :
      ∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ᶠ i in atTop, EqOn (L ∘ E i) (A i) W := by
    obtain ⟨D, hD, hKD, hDU⟩ := exists_compact_between hK hU hKU
    have hcompact : IsCompact (univ ×ˢ (Prod.snd '' D) : Set RoundCylinderSpace) :=
      isCompact_univ.prod (hD.image continuous_snd)
    have hdomain : univ ×ˢ (Prod.snd '' D) ⊆
        (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ : Set RoundCylinderSpace) := by
      rintro z ⟨hz, y, hy, hyz⟩
      exact ⟨hz, hyz ▸ (hDU hy).2⟩
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
      (hcompact.image_of_continuousOn (hΦ.continuousOn.mono hdomain))
    refine ⟨interior D, isOpen_interior, hKD, ?_⟩
    filter_upwards [eventually_ge_atTop j] with i hji x hx
    have hmem : F i x ∈ G.exhaustion i := G.exhaustion_monotone hji
      (hj (mem_image_of_mem Φ ⟨mem_univ _, mem_image_of_mem Prod.snd (interior_subset hx)⟩))
    have hΦx : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
        ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2) :=
      hΦ.contMDiffAt (hstrip.mem_nhds ⟨mem_univ _, (hDU (interior_subset hx)).2⟩)
    have hfs : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (f i)
        ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2) :=
      (((e i).terminalSpatialMap_contMDiffAt (G.exhaustion_open i) (t := 0) le_rfl hmem).comp
        ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2) hΦx).mdifferentiableAt (by simp)
    have hs := roundCylinderTensorCoefficient_pullback_eq
      ((S.term (G.subsequence i)).flow.flow.metric (τ i)) (q i) (f i) x hfs v w
    have hlim := roundCylinderTensorCoefficient_pullback_eq
      (G.limit.flow.flow.metric (τ i)) (q i) Φ x (hΦx.mdifferentiableAt (by simp)) v w
    exact (congrArg₂ (fun x y => x - y) hs hlim).symm
  change (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨V, hV, hxV, hs⟩ := hDlocal x hx
    obtain ⟨W, hW, hxW, heq⟩ := hnear {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW (mem_singleton x)⟩, ?_⟩
    filter_upwards [hs, heq] with i hi hEq
    exact (hi.mono inter_subset_left).congr (fun y hy => (hEq hy.2).symm)
  · intro m K hK hKU
    obtain ⟨W, hW, hKW, heq⟩ := hnear K hK hKU
    apply ((hDjet m K hK hKU).congr ?_).congr_right (fun _ _ => by simp [Function.comp_def])
    filter_upwards [heq] with i hi x hx
    exact (eqOn_iteratedFDeriv_of_isOpen hW hi m) (hKW hx)

end M23TerminalMetricConvergence

end PoincareConjecture
