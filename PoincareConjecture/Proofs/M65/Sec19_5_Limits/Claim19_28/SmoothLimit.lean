import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ActualSpatialBounds
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ChartNondegenerate
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture

open SpacetimeBounds.Bootstrap


private noncomputable def m65JetValues (n : ℕ) :
    Jet ℝ (M65ProjectedChartStateSpace n) 2 →L[ℝ] M65ProjectedChartJetSpace n where
  toFun z := (z 0 (fun _ => 1), z 1 (fun _ => 1), z 2 (fun _ => 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    exact ((continuous_eval_const (fun _ => 1)).comp (continuous_apply 0)).prodMk
      (((continuous_eval_const (fun _ => 1)).comp (continuous_apply 1)).prodMk
        ((continuous_eval_const (fun _ => 1)).comp (continuous_apply 2)))

private theorem m65JetValues_actual {n : ℕ}
    (Y : ℝ × ℝ → M65ProjectedChartStateSpace n) (z : ℝ × ℝ) :
    m65JetValues n (spatialJet 2 Y z) =
      (Y z, deriv (fun x => Y (z.1, x)) z.2,
        deriv (deriv (fun x => Y (z.1, x))) z.2) := by
  change (iteratedDeriv 0 (fun x => Y (z.1, x)) z.2,
    iteratedDeriv 1 (fun x => Y (z.1, x)) z.2,
    iteratedDeriv 2 (fun x => Y (z.1, x)) z.2) = _
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {a b : ℝ} {F : RicciFlow n M (Icc a b)}


private theorem m65StateSpatialBounds {κ : Type*} {circumference : κ → ℝ}
    (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k)) (p : M)
    {r s : ℝ} (hsub : Icc r s ⊆ Ioo a b) {K : Set M}
    (hKs : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (m : ℕ)
    (hv : ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      ‖iteratedFDeriv ℝ m (curveSpeed (P k).flow (c k) t) x‖ ≤ B)
    (hf : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s → (c k x t).1 ∈ K →
      ‖iteratedFDeriv ℝ m (m65IntrinsicChartField (P k) (c k) p j t) x‖ ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s → (c k x t).1 ∈ K →
      ‖iteratedFDeriv ℝ m (fun y => m65ProjectedChartState (P k) (c k) p (t, y)) x‖ ≤ B := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : ((E × ℝ) × (ℝ × (E × ℝ))) →L[ℝ] M65ProjectedChartStateSpace n :=
    { toFun := fun z => (z.1.2, (z.1.1, (z.2.1, z.2.2.2)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  obtain ⟨A, hA, ha⟩ := hv
  obtain ⟨B, hB, hb⟩ := hf 0
  obtain ⟨C, hC, hcB⟩ := hf 1
  refine ⟨‖L‖ * max B (max A C), mul_nonneg (norm_nonneg _)
    (hB.trans (le_max_left _ _)), ?_⟩
  intro k t x ht hx
  have h0 := m65IntrinsicChartField_contDiffAt (P k) (c k) (hc k) p 0
    (hsub ht) (hKs hx)
  have h1 := m65IntrinsicChartField_contDiffAt (P k) (c k) (hc k) p 1
    (hsub ht) (hKs hx)
  have hspeed : ContDiffAt ℝ ∞ (curveSpeed (P k).flow (c k) t) x :=
    ((M62.speed_joint_contDiffOn (P k).flow (c k) (hc k)).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, hsub ht⟩)).contDiffAt
  let f : ℝ → (E × ℝ) × (ℝ × (E × ℝ)) := fun y =>
    (m65IntrinsicChartField (P k) (c k) p 0 t y,
      curveSpeed (P k).flow (c k) t y, m65IntrinsicChartField (P k) (c k) p 1 t y)
  have hstate : (fun y => m65ProjectedChartState (P k) (c k) p (t, y)) = L ∘ f := rfl
  rw [hstate]
  apply (L.norm_iteratedFDeriv_comp_left (h0.prodMk (hspeed.prodMk h1))
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [iteratedFDeriv_prodMk h0 (hspeed.prodMk h1)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m), ContinuousMultilinearMap.opNorm_prod,
    iteratedFDeriv_prodMk hspeed h1
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m), ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max (hb k t x ht hx) (max_le_max (ha k t x ht) (hcB k t x ht hx))

omit [T2Space M] in
private theorem m65ActualStateFiniteJetRange {κ : Type*} {circumference : κ → ℝ}
    (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point) (p : M) {r s vmin : ℝ}
    (hsub : Icc r s ⊆ Ioo a b) (hvmin : 0 < vmin)
    {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (S : κ → Set (ℝ × ℝ))
    (hS : ∀ k z, z ∈ S k → z.1 ∈ Icc r s ∧ (c k z.2 z.1).1 ∈ K)
    (hv : ∀ k z, z ∈ S k → vmin ≤ curveSpeed (P k).flow (c k) z.1 z.2)
    (hspatial : ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ k z, z ∈ S k →
      ‖iteratedFDeriv ℝ m (fun x => m65ProjectedChartState (P k) (c k) p (z.1, x)) z.2‖ ≤ B)
    (j : ℕ) :
    ∃ C : Set (Jet ℝ (M65ProjectedChartStateSpace n) (2 + j)), IsCompact C ∧
      C ⊆ (baseProjection 2 j) ⁻¹'
        (m65JetValues n ⁻¹' m65ProjectedChartOperatorDomain (a := a) (b := b) p) ∧
      ∀ k, MapsTo (spatialJet (2 + j) (m65ProjectedChartState (P k) (c k) p)) (S k) C := by
  classical
  let V := M65ProjectedChartStateSpace n
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hH : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  choose B hB hb using hspatial
  let T : Jet ℝ V (2 + j) → V := fun z => (m65JetValues n (baseProjection 2 j z)).1
  have hT : Continuous T :=
    continuous_fst.comp ((m65JetValues n).continuous.comp (baseProjection 2 j).continuous)
  let D : Set V := Icc r s ×ˢ ((e '' K) ×ˢ (Ici vmin ×ˢ univ))
  have hD : IsClosed D := isClosed_Icc.prod (hH.isClosed.prod (isClosed_Ici.prod isClosed_univ))
  let C : Set (Jet ℝ V (2 + j)) :=
    {z | ∀ l : Fin (2 + j + 1), z l ∈ Metric.closedBall 0 (B l)} ∩ T ⁻¹' D
  have hball (l : Fin (2 + j + 1)) :
      IsCompact (Metric.closedBall (0 : ℝ [×(l : ℕ)]→L[ℝ] V) (B l)) := by
    have h := (isCompact_closedBall (0 : V) (B l)).image
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin (l : ℕ)) V).continuous
    simpa only [LinearIsometryEquiv.image_closedBall, map_zero] using h
  have hC : IsCompact C :=
    (isCompact_pi_infinite hball).inter_right (hD.preimage hT)
  refine ⟨C, hC, ?_, ?_⟩
  · intro z hz
    have hvalue : T z ∈ D := hz.2
    obtain ⟨q, hq, heq⟩ := hvalue.2.1
    refine ⟨hsub hvalue.1, ?_, hvmin.trans_le hvalue.2.2.1⟩
    change (T z).2.1 ∈ e.target
    rw [← heq]
    exact e.map_source (hKs hq)
  · intro k z hz
    constructor
    · intro l
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hb l k z hz
    · change T (spatialJet (2 + j) (m65ProjectedChartState (P k) (c k) p) z) ∈ D
      dsimp only [T]
      rw [baseProjection_spatialJet, m65JetValues_actual]
      exact ⟨(hS k z hz).1, ⟨_, (hS k z hz).2, rfl⟩, hv k z hz, mem_univ _⟩

private theorem m65ActualStateJointBounds {κ : Type*} {circumference : κ → ℝ}
    (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k)) (p : M) {r s vmin : ℝ}
    (hsub : Icc r s ⊆ Ioo a b) (hvmin : 0 < vmin)
    {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (J U : κ → Set ℝ) (S : κ → Set (ℝ × ℝ))
    (hJ : ∀ k, IsOpen (J k)) (hU : ∀ k, IsOpen (U k))
    (hrect : ∀ k, S k ⊆ J k ×ˢ U k)
    (htime : ∀ k, J k ⊆ Ioo a b)
    (hchart : ∀ k z, z ∈ J k ×ˢ U k →
      (c k z.2 z.1).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hS : ∀ k z, z ∈ S k → z.1 ∈ Icc r s ∧ (c k z.2 z.1).1 ∈ K)
    (hv : ∀ k z, z ∈ S k → vmin ≤ curveSpeed (P k).flow (c k) z.1 z.2)
    (hspatial : ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ k z, z ∈ S k →
      ‖iteratedFDeriv ℝ m (fun x => m65ProjectedChartState (P k) (c k) p (z.1, x)) z.2‖ ≤ B) :
    ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ k z, z ∈ S k →
      ‖iteratedFDeriv ℝ m (m65ProjectedChartState (P k) (c k) p) z‖ ≤ B := by
  let Ω := m65JetValues n ⁻¹' m65ProjectedChartOperatorDomain (a := a) (b := b) p
  let Q := m65ProjectedChartOperator F p ∘ m65JetValues n
  have hΩ : IsOpen Ω :=
    (m65ProjectedChartOperatorDomain_isOpen p).preimage (m65JetValues n).continuous
  have hQ : ContDiffOn ℝ ∞ Q Ω := (m65ProjectedChartOperator_contDiffOn F p).comp
    (m65JetValues n).contDiff.contDiffOn (fun _ hz => hz)
  have hf (k : κ) : ContDiffOn ℝ ∞ (m65ProjectedChartState (P k) (c k) p) (J k ×ˢ U k) :=
    fun z hz => (m65ProjectedChartState_contDiffAt (P k) (c k) (hc k) p
      (htime k hz.1) (hchart k z hz)).contDiffWithinAt
  have hrange (k : κ) (z : ℝ × ℝ) (hz : z ∈ J k ×ˢ U k) :
      spatialJet 2 (m65ProjectedChartState (P k) (c k) p) z ∈ Ω := by
    change m65JetValues n (spatialJet 2 (m65ProjectedChartState (P k) (c k) p) z) ∈
      m65ProjectedChartOperatorDomain (a := a) (b := b) p
    rw [m65JetValues_actual]
    exact m65ProjectedChartJet_mem_domain (P k) (c k) (hc k) p
      (htime k hz.1) (hchart k z hz)
  have hevol (k : κ) (z : ℝ × ℝ) (hz : z ∈ J k ×ˢ U k) :
      deriv (fun t => m65ProjectedChartState (P k) (c k) p (t, z.2)) z.1 =
        Q (spatialJet 2 (m65ProjectedChartState (P k) (c k) p) z) := by
    dsimp only [Q, Function.comp_apply]
    rw [m65JetValues_actual]
    exact (m65ProjectedChartState_equation (P k) (c k) (hc k) p
      (htime k hz.1) (hchart k z hz)).deriv
  have hfinite (j : ℕ) := m65ActualStateFiniteJetRange P c p hsub hvmin hK hKs
    S hS hv hspatial j
  have h := eventuallyBounded_spacetime_jets (⊤ : Filter κ) hΩ hQ
    (fun k => m65ProjectedChartState (P k) (c k) p) J U S hf hJ hU hrect hrange hevol
    (fun j => by
      obtain ⟨B, hB, hb⟩ := hspatial j
      exact ⟨B, hB, Eventually.of_forall hb⟩)
    (fun j => by
      obtain ⟨C, hC, hCd, hCr⟩ := hfinite j
      exact ⟨C, hC, hCd, Eventually.of_forall hCr⟩)
  simpa only [EventuallyBoundedJet, eventually_top] using h


omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M] in
private theorem m65C0_chart_rectangle {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    {f : ℕ → C(Ω, M)} {q : C(Ω, M)} (hseq : Tendsto f atTop (𝓝 q))
    (z : Ω) {V : Set M} (hV : IsOpen V) (hzV : q z ∈ V) :
    ∃ J U : Set ℝ, IsOpen J ∧ IsOpen U ∧ z.1.1 ∈ J ∧ z.1.2 ∈ U ∧
      ∃ hJU : J ×ˢ U ⊆ Ω, (∀ w (hw : w ∈ J ×ˢ U), q ⟨w, hJU hw⟩ ∈ V) ∧
        ∀ᶠ k in atTop, ∀ w (hw : w ∈ J ×ˢ U), f k ⟨w, hJU hw⟩ ∈ V := by
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have hpair : Tendsto (fun v : ℕ × Ω => (f v.1, v.2)) (atTop ×ˢ 𝓝 z) (𝓝 (q, z)) :=
    (hseq.comp tendsto_fst).prodMk_nhds tendsto_snd
  have heval : Tendsto (fun v : ℕ × Ω => f v.1 v.2) (atTop ×ˢ 𝓝 z) (𝓝 (q z)) :=
    (continuous_eval.tendsto (q, z)).comp hpair
  obtain ⟨pa, hpa, pb, hpb, hab⟩ :=
    eventually_prod_iff.mp (heval (hV.mem_nhds hzV))
  obtain ⟨W, hWsub, hW, hzW⟩ := mem_nhds_iff.mp
    (inter_mem hpb (q.continuous.continuousAt (hV.mem_nhds hzV)))
  have hO : IsOpen (Subtype.val '' W : Set (ℝ × ℝ)) := hΩ.isOpenMap_subtype_val W hW
  obtain ⟨J, U, hJ, hzJ, hU, hzU, hJU'⟩ :=
    mem_nhds_prod_iff'.mp (hO.mem_nhds ⟨z, hzW, rfl⟩)
  have hJU : J ×ˢ U ⊆ Ω := by
    intro w hw
    obtain ⟨y, _hy, rfl⟩ := hJU' hw
    exact y.property
  refine ⟨J, U, hJ, hU, hzJ, hzU, hJU, ?_, ?_⟩
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := hJU' hw
    exact (hWsub hy).2
  · filter_upwards [hpa] with k hk w hw
    obtain ⟨y, hy, rfl⟩ := hJU' hw
    exact hab hk (hWsub hy).1

private theorem m65LocalSmoothLimit
    {circumference : ℕ → ℝ} (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k)) (p : M)
    {r s vmin : ℝ} (hsub : Icc r s ⊆ Ioo a b) (hvmin : 0 < vmin)
    {J U : Set ℝ} (hJ : IsOpen J) (hU : IsOpen U) (hJtime : J ⊆ Icc r s)
    {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hcore : ∀ k z, z ∈ J ×ˢ U → (c k z.2 z.1).1 ∈ K)
    (hv : ∀ k z, z ∈ J ×ˢ U → vmin ≤ curveSpeed (P k).flow (c k) z.1 z.2)
    (hu : ∀ z ∈ J ×ˢ U, Tendsto (fun k => m62Slope (P k) (c k) z.1 z.2) atTop (𝓝 0))
    (hspatial : ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ k z, z ∈ J ×ˢ U →
      ‖iteratedFDeriv ℝ m (fun x => m65ProjectedChartState (P k) (c k) p (z.1, x)) z.2‖ ≤ B)
    (q : ℝ × ℝ → M) (hq : MapsTo q (J ×ˢ U) K)
    (hC0 : ∀ z ∈ J ×ˢ U, Tendsto (fun k => (c k z.2 z.1).1) atTop (𝓝 (q z))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Y : ℝ × ℝ → M65ProjectedChartStateSpace n,
      ContDiffOn ℝ ∞ Y (J ×ˢ U) ∧
      (∀ m C, IsCompact C → C ⊆ J ×ˢ U → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (m65ProjectedChartState (P (σ k)) (c (σ k)) p))
        (iteratedFDeriv ℝ m Y) atTop C) ∧
      (∀ z ∈ J ×ˢ U, (Y z).1 = z.1 ∧
        (Y z).2.1 = (chartAt (EuclideanSpace ℝ (Fin n)) p) (q z) ∧
        vmin ≤ (Y z).2.2.1 ∧ (Y z).2.2.2 = 0) ∧
      (∀ z ∈ J ×ˢ U, m65FlowChartMetric F p (z.1, (Y z).2.1)
          (fderiv ℝ Y z (0, 1)).2.1 (fderiv ℝ Y z (0, 1)).2.1 = (Y z).2.2.1 ^ 2 ∧
        (fderiv ℝ Y z (0, 1)).2.1 ≠ 0) ∧
      ∀ z ∈ J ×ˢ U, HasDerivAt (fun t => Y (t, z.2))
        (m65ProjectedChartOperator F p (m65LimitChartJet Y z)) z.1 := by
  have hchart (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ J ×ˢ U) := hKs (hcore k z hz)
  have hfull := m65ActualStateJointBounds P c hc p hsub hvmin hK hKs
    (fun _ => J) (fun _ => U) (fun _ => J ×ˢ U) (fun _ => hJ) (fun _ => hU)
    (fun _ => subset_rfl) (fun _ => hJtime.trans hsub) hchart
    (fun k z hz => ⟨hJtime hz.1, hcore k z hz⟩) hv hspatial
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  have htarget : e '' K ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hKs hx)
  obtain ⟨σ, hσ, Y, hY, hjet, hval, heq⟩ := m65ProjectedChart_exists_smooth_limit
    P c hc p (hJ.prod hU) (fun z hz => hsub (hJtime hz.1)) hchart
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)) htarget
    (fun k z hz => ⟨_, hcore k z hz, rfl⟩) hvmin hv hu (fun C _hC hCrect m => by
      obtain ⟨B, _hB, hb⟩ := hfull m
      exact ⟨B, Eventually.of_forall (fun k z hz => hb k z (hCrect hz))⟩)
  have hposition (z : ℝ × ℝ) (hz : z ∈ J ×ˢ U) : (Y z).2.1 = e (q z) := by
    have hraw := (hjet 0 {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at
      (mem_singleton z)
    have hstate : Tendsto (fun k => m65ProjectedChartState (P (σ k)) (c (σ k)) p z)
        atTop (𝓝 (Y z)) := by
      have h := ((continuous_eval_const (fun _ : Fin 0 => (0, 0))).tendsto _).comp hraw
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using h
    exact tendsto_nhds_unique hstate.snd_nhds.fst_nhds
      ((e.continuousAt (hKs (hq hz))).tendsto.comp ((hC0 z hz).comp hσ.tendsto_atTop))
  refine ⟨σ, hσ, Y, hY, hjet, ?_, ?_, heq⟩
  · intro z hz
    exact ⟨(hval z hz).1, hposition z hz, (hval z hz).2.2⟩
  · intro z hz
    exact m65ProjectedChart_limit_nondegenerate (fun k => P (σ k))
      (fun k => c (σ k)) (fun k => hc (σ k)) p (fun k => hchart (σ k)) hjet hz
      (hsub (hJtime hz.1)) (htarget (hval z hz).2.1)
      (hvmin.trans_le (hval z hz).2.2.1) (hval z hz).2.2.2

private theorem m65LocalChartCurve_geometry (p : M) (c : ℝ → ℝ → M)
    (q : ℝ × ℝ → EuclideanSpace ℝ (Fin n)) (v : ℝ × ℝ → ℝ)
    {J U : Set ℝ} (hJ : IsOpen J) (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q (J ×ˢ U)) (hv : ContDiffOn ℝ ∞ v (J ×ˢ U))
    (hsource : ∀ z ∈ J ×ˢ U, c z.2 z.1 ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hrep : ∀ z ∈ J ×ˢ U, q z = (chartAt (EuclideanSpace ℝ (Fin n)) p) (c z.2 z.1))
    (hpos : ∀ z ∈ J ×ˢ U, 0 < v z)
    (hmetric : ∀ z ∈ J ×ˢ U, m65FlowChartMetric F p (z.1, q z)
      (deriv (fun y => q (z.1, y)) z.2) (deriv (fun y => q (z.1, y)) z.2) = v z ^ 2)
    (heq : ∀ z ∈ J ×ˢ U, HasDerivAt (fun t => q (t, z.2))
      ((v z ^ 2)⁻¹ • (deriv (deriv (fun y => q (z.1, y))) z.2 +
        M04.shiChartChristoffel (F.connection z.1)
          (chartAt (EuclideanSpace ℝ (Fin n)) p) (q z)
          (deriv (fun y => q (z.1, y)) z.2) (deriv (fun y => q (z.1, y)) z.2)) -
        (deriv (fun y => v (z.1, y)) z.2 / v z ^ 3) •
          deriv (fun y => q (z.1, y)) z.2) z.1) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun z => c z.2 z.1) (J ×ˢ U) ∧
      ∀ z ∈ J ×ˢ U, curveSpeed F c z.1 z.2 = v z ∧
        curveVelocity (n := n) (fun y => c y z.1) z.2 ≠ 0 ∧
        curveVelocity (n := n) (fun t => c z.2 t) z.1 = m62CurvatureVector F c z.1 z.2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E p
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z => c z.2 z.1) (J ×ˢ U) := by
    have h := hi.comp hq.contMDiffOn (fun z hz => by
      change q z ∈ e.target
      rw [hrep z hz]
      exact e.map_source (hsource z hz))
    apply h.congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [hrep z hz, e.left_inv (hsource z hz)]
  have hcs (t : ℝ) (ht : t ∈ J) :
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x t) U :=
    hcurve.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
      (fun _ hx => ⟨ht, hx⟩)
  have hqs (t : ℝ) (ht : t ∈ J) : ContDiffOn ℝ ∞ (fun x => q (t, x)) U :=
    hq.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => ⟨ht, hx⟩)
  have hvs (t : ℝ) (ht : t ∈ J) : ContDiffOn ℝ ∞ (fun x => v (t, x)) U :=
    hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => ⟨ht, hx⟩)
  have hcoord (t x : ℝ) (ht : t ∈ J) (hx : x ∈ U) :
      deriv (fun y => q (t, y)) x =
        mfderiv (𝓡 n) (𝓡 n) e (c x t) (curveVelocity (fun y => c y t) x) := by
    have h := Proofs.M09.hasDerivAt_chart_curve p (fun y => c y t) x
      (hsource (t, x) ⟨ht, hx⟩)
      (((hcs t ht).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    exact (h.congr_of_eventuallyEq (by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hrep (t, y) ⟨ht, hy⟩)).deriv
  have hspeed (t x : ℝ) (ht : t ∈ J) (hx : x ∈ U) : curveSpeed F c t x = v (t, x) := by
    have h := hmetric (t, x) ⟨ht, hx⟩
    rw [hrep (t, x) ⟨ht, hx⟩, hcoord t x ht hx,
      m65FlowChartMetric_at_source F p t (hsource (t, x) ⟨ht, hx⟩)] at h
    change Real.sqrt _ = _
    rw [h, Real.sqrt_sq (hpos (t, x) ⟨ht, hx⟩).le]
  refine ⟨hcurve, ?_⟩
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have hz : (t, x) ∈ J ×ˢ U := ⟨ht, hx⟩
  have hv0 : v (t, x) ≠ 0 := (hpos (t, x) hz).ne'
  refine ⟨hspeed t x ht hx, ?_, ?_⟩
  · intro hzero
    have h := hspeed t x ht hx
    simp only [curveSpeed, RiemannianMetric.tangentNorm, hzero, map_zero,
      Real.sqrt_zero] at h
    exact hv0 h.symm
  · let w : ℝ → E := fun y => (v (t, y))⁻¹ • deriv (fun z => q (t, z)) y
    have hw : ContDiffOn ℝ ∞ w U :=
      ((hvs t ht).inv (fun y hy => (hpos (t, y) ⟨ht, hy⟩).ne')).smul
        ((hqs t ht).deriv_of_isOpen hU (by simp))
    have hgerm : spatialUnitTangent F c t =ᶠ[𝓝 x]
        (fun y => Proofs.M09.chartVectorField p (w y) (c y t)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      have hh := Proofs.M09.chartVectorField_differential p (c y t)
        (spatialUnitTangent F c t y) (hsource (t, y) ⟨ht, hy⟩)
      rw [show mfderiv (𝓡 n) (𝓡 n) e (c y t) (spatialUnitTangent F c t y) = w y by
        dsimp only [spatialUnitTangent, w]
        rw [map_smul, hspeed t y ht hy, ← hcoord t y ht hy]] at hh
      exact hh.symm
    have hcov := M62.pullback_chart_field_coordinates (F.connection t) p
      (((hcs t ht).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      (hsource (t, x) hz) hU hx w hw
    rw [← M62.pullback_congr (F.connection t) hgerm, ← hcoord t x ht hx] at hcov
    have hdv := ((hvs t ht).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdq : DifferentiableAt ℝ (deriv (fun y => q (t, y))) x :=
      (((hqs t ht).deriv_of_isOpen hU (m := ∞) (by simp)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdw : deriv w x = (v (t, x))⁻¹ • deriv (deriv (fun y => q (t, y))) x +
        (-deriv (fun y => v (t, y)) x / v (t, x) ^ 2) • deriv (fun y => q (t, y)) x :=
      ((hdv.hasDerivAt.inv hv0).smul hdq.hasDerivAt).deriv
    have htime : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun τ => c x τ) J :=
      hcurve.comp (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn
        (fun _ hτ => ⟨hτ, hx⟩)
    have hct := Proofs.M09.hasDerivAt_chart_curve p (fun τ => c x τ) t
      (hsource (t, x) hz)
      ((htime.contMDiffAt (hJ.mem_nhds ht)).mdifferentiableAt (by simp))
    have hct' := hct.congr_of_eventuallyEq (by
      filter_upwards [hJ.mem_nhds ht] with τ hτ
      exact hrep (τ, x) ⟨hτ, hx⟩)
    have he := (M04.shiChart_mfderiv_isInvertible
      (contMDiffOn_chart (I := 𝓡 n)) (contMDiffOn_chart_symm (I := 𝓡 n))
      (hsource (t, x) hz))
    apply he.injective
    rw [hct'.unique (heq (t, x) hz)]
    change _ = mfderiv (𝓡 n) (𝓡 n) e (c x t)
      ((curveSpeed F c t x)⁻¹ • _)
    rw [map_smul, hspeed t x ht hx, hcov, hdw]
    dsimp only [w]
    rw [← hrep (t, x) hz]
    simp only [map_smul, smul_add, smul_smul]
    have ha : (v (t, x))⁻¹ * (v (t, x))⁻¹ = (v (t, x) ^ 2)⁻¹ := by ring
    have hb : (v (t, x))⁻¹ * (-(deriv (fun y => v (t, y)) x) / v (t, x) ^ 2) =
        -(deriv (fun y => v (t, y)) x / v (t, x) ^ 3) := by field_simp
    rw [ha, hb, neg_smul, sub_eq_add_neg]
    abel

private theorem m65Linear_spatialJet {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) {Y : ℝ × ℝ → V} {t x : ℝ}
    (hY : ContDiffAt ℝ ∞ Y (t, x)) :
    deriv (fun y => L (Y (t, y))) x = L (fderiv ℝ Y (t, x) (0, 1)) ∧
      deriv (deriv (fun y => L (Y (t, y)))) x =
        L (iteratedFDeriv ℝ 2 Y (t, x) (fun _ => (0, 1))) := by
  have hd := (hY.differentiableAt (by simp)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  refine ⟨(L.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt).deriv, ?_⟩
  have hfirst : deriv (fun y : ℝ => (t, y)) = fun _ => (0, 1) := by
    funext y
    exact ((hasDerivAt_const y t).prodMk (hasDerivAt_id y)).deriv
  have h := iteratedDeriv_vcomp_two
    ((L.contDiff.contDiffAt.comp (t, x) hY).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (show ContDiffAt ℝ 2 (fun y : ℝ => (t, y)) x by fun_prop)
  rw [L.iteratedFDeriv_comp_left hY (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)] at h
  simpa only [Function.comp_def, iteratedDeriv_succ, iteratedDeriv_zero,
    hfirst, deriv_const, map_zero, add_zero,
    ContinuousLinearMap.compContinuousMultilinearMap_coe] using h

private theorem m65LocalState_geometry (p : M) (c : ℝ → ℝ → M)
    {Y : ℝ × ℝ → M65ProjectedChartStateSpace n} {J U : Set ℝ}
    (hJ : IsOpen J) (hU : IsOpen U) (hY : ContDiffOn ℝ ∞ Y (J ×ˢ U))
    (hsource : ∀ z ∈ J ×ˢ U, c z.2 z.1 ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hrep : ∀ z ∈ J ×ˢ U, (Y z).1 = z.1 ∧
      (Y z).2.1 = (chartAt (EuclideanSpace ℝ (Fin n)) p) (c z.2 z.1) ∧ 0 < (Y z).2.2.1)
    (hmetric : ∀ z ∈ J ×ˢ U, m65FlowChartMetric F p (z.1, (Y z).2.1)
      (fderiv ℝ Y z (0, 1)).2.1 (fderiv ℝ Y z (0, 1)).2.1 = (Y z).2.2.1 ^ 2)
    (heq : ∀ z ∈ J ×ˢ U, HasDerivAt (fun t => Y (t, z.2))
      (m65ProjectedChartOperator F p (m65LimitChartJet Y z)) z.1) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun z => c z.2 z.1) (J ×ˢ U) ∧
      ∀ z ∈ J ×ˢ U, curveSpeed F c z.1 z.2 = (Y z).2.2.1 ∧
        curveVelocity (n := n) (fun y => c y z.1) z.2 ≠ 0 ∧
        curveVelocity (n := n) (fun t => c z.2 t) z.1 = m62CurvatureVector F c z.1 z.2 := by
  let L : M65ProjectedChartStateSpace n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun y => y.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  let V : M65ProjectedChartStateSpace n →L[ℝ] ℝ :=
    { toFun := fun y => y.2.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  have hjet (z : ℝ × ℝ) (hz : z ∈ J ×ˢ U) :
      deriv (fun y => (Y (z.1, y)).2.1) z.2 = (fderiv ℝ Y z (0, 1)).2.1 ∧
        deriv (deriv (fun y => (Y (z.1, y)).2.1)) z.2 =
          (iteratedFDeriv ℝ 2 Y z (fun _ => (0, 1))).2.1 :=
    m65Linear_spatialJet L (hY.contDiffAt ((hJ.prod hU).mem_nhds hz))
  have hvjet (z : ℝ × ℝ) (hz : z ∈ J ×ˢ U) :
      deriv (fun y => (Y (z.1, y)).2.2.1) z.2 = (fderiv ℝ Y z (0, 1)).2.2.1 :=
    (m65Linear_spatialJet V (hY.contDiffAt ((hJ.prod hU).mem_nhds hz))).1
  apply m65LocalChartCurve_geometry p c (fun z => (Y z).2.1) (fun z => (Y z).2.2.1)
    hJ hU hY.snd.fst hY.snd.snd.fst hsource (fun z hz => (hrep z hz).2.1)
    (fun z hz => (hrep z hz).2.2)
  · intro z hz
    rw [(hjet z hz).1]
    exact hmetric z hz
  · intro z hz
    have h := L.hasFDerivAt.comp_hasDerivAt z.1 (heq z hz)
    change HasDerivAt (fun t => (Y (t, z.2)).2.1) _ z.1 at h
    change HasDerivAt _ (m65ChartHorizontalCurvature F p (m65LimitChartJet Y z)) _ at h
    rw [(hjet z hz).1, (hjet z hz).2, hvjet z hz]
    dsimp only [m65ChartHorizontalCurvature, m65LimitChartJet] at h
    rw [(hrep z hz).1] at h
    exact h

private theorem m65Jets_of_pointwise {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (f : ℕ → ℝ × ℝ → V)
    (hf : ∀ k, ContDiffOn ℝ ∞ (f k) Ω)
    (hb : ∀ m, ∃ B : ℝ, ∀ k z, z ∈ Ω → ‖iteratedFDeriv ℝ m (f k) z‖ ≤ B)
    {g : ℝ × ℝ → V} (hg : ∀ z ∈ Ω, Tendsto (fun k => f k z) atTop (𝓝 (g z)))
    (m : ℕ) {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m g) atTop C := by
  let fs := fun k => UniformFun.ofFun (fun z : C => iteratedFDeriv ℝ m (f k) z)
  let gs := UniformFun.ofFun (fun z : C => iteratedFDeriv ℝ m g z)
  have ht : Tendsto fs atTop (𝓝 gs) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨σ, hσ, Y, _hY, hjet⟩ :=
      Poincare.Analysis.Calculus.exists_common_smoothSubsequenceExtraction_finiteDimensional
        (E := fun _ : ℕ => ℝ × ℝ) (F := fun _ : ℕ => V)
        (fun _ => hΩ) (fun _ k => f (ns k)) (fun _ k => hf (ns k))
        (fun _ K _hK hKΩ l => by
          obtain ⟨B, hB⟩ := hb l
          exact ⟨B, Eventually.of_forall (fun k z hz => hB (ns k) z (hKΩ hz))⟩)
    have heq : EqOn (Y 0) g Ω := by
      intro z hz
      have hzero := (hjet 0 0 {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at
        (mem_singleton z)
      have hval : Tendsto (fun k => f (ns (σ k)) z) atTop (𝓝 (Y 0 z)) := by
        simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
          ((continuous_eval_const (fun _ : Fin 0 => (0, 0))).tendsto _).comp hzero
      exact tendsto_nhds_unique hval ((hg z hz).comp (hns.comp hσ.tendsto_atTop))
    have hsame : EqOn (iteratedFDeriv ℝ m (Y 0)) (iteratedFDeriv ℝ m g) C := by
      intro z hz
      have hn : Y 0 =ᶠ[𝓝 z] g := by
        filter_upwards [hΩ.mem_nhds (hCΩ hz)] with w hw
        exact heq hw
      exact (hn.iteratedFDeriv ℝ m).self_of_nhds
    exact ⟨σ, UniformFun.tendsto_iff_tendstoUniformly.mpr
      (tendstoUniformlyOn_iff_restrict.mp ((hjet 0 m C hC hCΩ).congr_right hsame))⟩
  exact tendstoUniformlyOn_iff_restrict.mpr (UniformFun.tendsto_iff_tendstoUniformly.mp ht)

set_option maxHeartbeats 2400000 in







theorem m65Projected_exists_smooth_curveShortening_limit
    (hcompact : IsCompact (univ : Set M)) {circumference : ℕ → ℝ}
    (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k))
    {r s C vmin : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b)
    (hC : 0 ≤ C) (hRm : ∀ t ∈ Icc r s, ∀ q, (F.connection t).curvatureTensorNorm q ≤ C)
    (v₀ : ℕ → ℝ) (hinit : ∀ k x, curveSpeed (P k).flow (c k) r x = v₀ k)
    (hvzero : ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      |curveSpeed (P k).flow (c k) t x| ≤ B)
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      ((P k).flow.metric t).tangentNorm (c k x t)
        (m65IntrinsicTangentJet (P k).flow (c k) j t x) ≤ B)
    (hvmin : 0 < vmin) (hlower : ∀ k t x, t ∈ Icc r s →
      vmin ≤ curveSpeed (P k).flow (c k) t x)
    (hu : ∀ t ∈ Ioo r s, ∀ x,
      Tendsto (fun k => m62Slope (P k) (c k) t x) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ clim : ℝ → ℝ → M,
      (∀ t ∈ Ioo r s, ∀ x, Tendsto (fun k => (c (σ k) x t).1) atTop (𝓝 (clim x t))) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun z => clim z.2 z.1) (Ioo r s ×ˢ univ) ∧
      (∀ t ∈ Ioo r s, ∀ x, clim (x + curvePeriod) t = clim x t) ∧
      (∀ t ∈ Ioo r s, ∀ x, vmin ≤ curveSpeed F clim t x ∧
        curveVelocity (n := n) (fun y => clim y t) x ≠ 0 ∧
        curveVelocity (n := n) (fun τ => clim x τ) t = m62CurvatureVector F clim t x) ∧
      ∀ z ∈ Ioo r s ×ˢ (univ : Set ℝ), ∃ (p : M) (J U : Set ℝ),
        IsOpen J ∧ IsOpen U ∧ z.1 ∈ J ∧ z.2 ∈ U ∧ J ×ˢ U ⊆ Ioo r s ×ˢ univ ∧
        (∀ w ∈ J ×ˢ U, clim w.2 w.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) ∧
        ∀ m K, IsCompact K → K ⊆ J ×ˢ U → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (fun w : ℝ × ℝ =>
            (chartAt (EuclideanSpace ℝ (Fin n)) p) (c (σ k) w.2 w.1).1))
          (iteratedFDeriv ℝ m (fun w : ℝ × ℝ =>
            (chartAt (EuclideanSpace ℝ (Fin n)) p) (clim w.2 w.1))) atTop K := by
  classical
  obtain ⟨N, p, K, hK, hKs, hcover, hspatial⟩ :=
    m65ActualIntrinsicSpatialBounds hcompact P c hc hrs hsub v₀ hinit hvzero hbound
  obtain ⟨B₀, hB₀, hspeed⟩ := hvzero
  obtain ⟨B₁, hB₁, hcurv⟩ := hbound 1
  obtain ⟨σ, hσ, q, hseq⟩ := m65Projected_exists_continuous_subsequence hcompact P c hc
    hrs hsub hC hB₀ hB₁ hRm (fun k t x ht => (le_abs_self _).trans (hspeed k t x ht))
    (fun k t x ht => hcurv k t x ht)
  let Ω : Set (ℝ × ℝ) := Ioo r s ×ˢ univ
  let clim : ℝ → ℝ → M := fun x t => if h : (t, x) ∈ Ω then q ⟨(t, x), h⟩ else (c 0 0 r).1
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hrep (z : ℝ × ℝ) (hz : z ∈ Ω) : clim z.2 z.1 = q ⟨z, hz⟩ := dif_pos hz
  have hpoint (z : ℝ × ℝ) (hz : z ∈ Ω) :
      Tendsto (fun k => (c (σ k) z.2 z.1).1) atTop (𝓝 (clim z.2 z.1)) := by
    rw [hrep z hz]
    exact ((continuous_eval_const (⟨z, hz⟩ : Ω)).tendsto q).comp hseq
  have hlocal (z : ℝ × ℝ) (hz : z ∈ Ω) :
      ∃ (p : M) (J U : Set ℝ), IsOpen J ∧ IsOpen U ∧ z.1 ∈ J ∧ z.2 ∈ U ∧ J ×ˢ U ⊆ Ω ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun w => clim w.2 w.1) (J ×ˢ U) ∧
        (∀ w ∈ J ×ˢ U, vmin ≤ curveSpeed F clim w.1 w.2 ∧
          curveVelocity (n := n) (fun y => clim y w.1) w.2 ≠ 0 ∧
          curveVelocity (n := n) (fun τ => clim w.2 τ) w.1 = m62CurvatureVector F clim w.1 w.2) ∧
        (∀ w ∈ J ×ˢ U, clim w.2 w.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) ∧
        ∀ m D, IsCompact D → D ⊆ J ×ˢ U → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (fun w : ℝ × ℝ =>
            (chartAt (EuclideanSpace ℝ (Fin n)) p) (c (σ k) w.2 w.1).1))
          (iteratedFDeriv ℝ m (fun w : ℝ × ℝ =>
            (chartAt (EuclideanSpace ℝ (Fin n)) p) (clim w.2 w.1))) atTop D := by
    obtain ⟨i, hi⟩ := hcover (q ⟨z, hz⟩)
    obtain ⟨J, U, hJ, hU, hzJ, hzU, hJU, hqK, htail⟩ :=
      m65C0_chart_rectangle hΩ hseq ⟨z, hz⟩ isOpen_interior hi
    obtain ⟨l, hl⟩ := eventually_atTop.mp htail
    let τ : ℕ → ℕ := fun k => σ (k + l)
    have hτ : Tendsto τ atTop atTop := hσ.tendsto_atTop.comp (tendsto_add_atTop_nat l)
    have hcore (k : ℕ) (w : ℝ × ℝ) (hw : w ∈ J ×ˢ U) : (c (τ k) w.2 w.1).1 ∈ K i :=
      interior_subset (hl (k + l) (Nat.le_add_left l k) w hw)
    have hlimitcore (w : ℝ × ℝ) (hw : w ∈ J ×ˢ U) : clim w.2 w.1 ∈ K i := by
      rw [hrep w (hJU hw)]
      exact interior_subset (hqK w hw)
    have hJtime : J ⊆ Icc r s := by
      intro t ht
      have h : (t, z.2) ∈ Ω := hJU ⟨ht, hzU⟩
      exact Ioo_subset_Icc_self h.1
    have hstate : ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ k w, w ∈ J ×ˢ U →
        ‖iteratedFDeriv ℝ m
          (fun x => m65ProjectedChartState (P (τ k)) (c (τ k)) (p i) (w.1, x)) w.2‖ ≤ B := by
      intro m
      obtain ⟨B, hB, hb⟩ := m65StateSpatialBounds P c hc (p i) hsub (hKs i) m
        (hspatial m).1 ((hspatial m).2 i)
      exact ⟨B, hB, fun k w hw => hb (τ k) w.1 w.2 (hJtime hw.1) (hcore k w hw)⟩
    have hlo (k : ℕ) (w : ℝ × ℝ) (hw : w ∈ J ×ˢ U) := hlower (τ k) w.1 w.2 (hJtime hw.1)
    have hp (w : ℝ × ℝ) (hw : w ∈ J ×ˢ U) :
        Tendsto (fun k => (c (τ k) w.2 w.1).1) atTop (𝓝 (clim w.2 w.1)) :=
      (hpoint w (hJU hw)).comp (tendsto_add_atTop_nat l)
    obtain ⟨_ρ, _hρ, Y, hY, _hjets, hval, hmetric, heq⟩ := m65LocalSmoothLimit
      (fun k => P (τ k)) (fun k => c (τ k)) (fun k => hc (τ k)) (p i) hsub hvmin
      hJ hU hJtime (hK i) (hKs i) hcore hlo
      (fun w hw => (hu w.1 (hJU hw).1 w.2).comp hτ) hstate
      (fun w => clim w.2 w.1) (fun w hw => hlimitcore w hw) hp
    have hsource := fun w hw => hKs i (hlimitcore w hw)
    obtain ⟨hsmooth, hgeom⟩ := m65LocalState_geometry (p i) clim hJ hU hY hsource
      (fun w hw => ⟨(hval w hw).1, (hval w hw).2.1, hvmin.trans_le (hval w hw).2.2.1⟩)
      (fun w hw => (hmetric w hw).1) heq
    refine ⟨p i, J, U, hJ, hU, hzJ, hzU, hJU, hsmooth, ?_, hsource, ?_⟩
    · intro w hw
      exact ⟨(hgeom w hw).1 ▸ (hval w hw).2.2.1, (hgeom w hw).2⟩
    · have hchart := fun k w hw => hKs i (hcore k w hw)
      have hjoint := m65ActualStateJointBounds
        (fun k => P (τ k)) (fun k => c (τ k)) (fun k => hc (τ k)) (p i) hsub hvmin
        (hK i) (hKs i) (fun _ => J) (fun _ => U) (fun _ => J ×ˢ U)
        (fun _ => hJ) (fun _ => hU) (fun _ => subset_rfl)
        (fun _ => hJtime.trans hsub) hchart
        (fun k w hw => ⟨hJtime hw.1, hcore k w hw⟩) hlo hstate
      let L : M65ProjectedChartStateSpace n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        { toFun := fun y => y.2.1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          cont := by fun_prop }
      let f : ℕ → ℝ × ℝ → EuclideanSpace ℝ (Fin n) := fun k w =>
        (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (c (τ k) w.2 w.1).1
      have hf (k : ℕ) : ContDiffOn ℝ ∞ (f k) (J ×ˢ U) := by
        intro w hw
        exact (L.contDiff.contDiffAt.comp w (m65ProjectedChartState_contDiffAt
          (P (τ k)) (c (τ k)) (hc (τ k)) (p i)
          (hsub (hJtime hw.1)) (hchart k w hw))).contDiffWithinAt
      have hb (m : ℕ) : ∃ B : ℝ, ∀ k w, w ∈ J ×ˢ U → ‖iteratedFDeriv ℝ m (f k) w‖ ≤ B := by
        obtain ⟨B, _hB, hb⟩ := hjoint m
        refine ⟨‖L‖ * B, ?_⟩
        intro k w hw
        exact (L.norm_iteratedFDeriv_comp_left (m65ProjectedChartState_contDiffAt
          (P (τ k)) (c (τ k)) (hc (τ k)) (p i) (hsub (hJtime hw.1)) (hchart k w hw))
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).trans
          (mul_le_mul_of_nonneg_left (hb k w hw) (norm_nonneg L))
      have hfp (w : ℝ × ℝ) (hw : w ∈ J ×ˢ U) : Tendsto (fun k => f k w) atTop
          (𝓝 ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (clim w.2 w.1))) :=
        (((chartAt (EuclideanSpace ℝ (Fin n)) (p i)).continuousAt
          (hsource w hw)).tendsto).comp (hp w hw)
      intro m D hD hDrect
      have ht := m65Jets_of_pointwise (hJ.prod hU) f hf hb hfp m hD hDrect
      apply tendstoUniformlyOn_iff_restrict.mpr
      apply UniformFun.tendsto_iff_tendstoUniformly.mp
      exact (tendsto_add_atTop_iff_nat l).mp
        (UniformFun.tendsto_iff_tendstoUniformly.mpr (tendstoUniformlyOn_iff_restrict.mp ht))
  refine ⟨σ, hσ, clim, (fun t ht x => hpoint (t, x) ⟨ht, mem_univ _⟩), ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨_, J, U, hJ, hU, hzJ, hzU, _, hsmooth, _⟩ := hlocal z hz
    exact (hsmooth.contMDiffAt ((hJ.prod hU).mem_nhds ⟨hzJ, hzU⟩)).contMDiffWithinAt
  · intro t ht x
    have hleft := hpoint (t, x + curvePeriod) ⟨ht, mem_univ _⟩
    have hright := hpoint (t, x) ⟨ht, mem_univ _⟩
    exact tendsto_nhds_unique
      (hleft.congr (fun k => congrArg Prod.fst ((hc (σ k)).periodic t
        (Ioo_subset_Icc_self (hsub (Ioo_subset_Icc_self ht))) x))) hright
  · intro t ht x
    obtain ⟨_, _, _, _, _, htJ, hxU, _, _, hg, _⟩ := hlocal (t, x) ⟨ht, mem_univ _⟩
    exact hg (t, x) ⟨htJ, hxU⟩
  · intro z hz
    obtain ⟨p, J, U, hJ, hU, hzJ, hzU, hJU, _, _, hs, hj⟩ := hlocal z hz
    exact ⟨p, J, U, hJ, hU, hzJ, hzU, hJU, hs, hj⟩

end PoincareConjecture
