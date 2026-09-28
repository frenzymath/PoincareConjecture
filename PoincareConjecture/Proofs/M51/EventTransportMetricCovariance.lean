import PoincareConjecture.Proofs.M51.EventTransportMetricPullback
import PoincareConjecture.Proofs.M51.LimitPullback

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M51EventTransport

local notation "V3" => EuclideanSpace ℝ (Fin 3)
local notation "Bil3" => V3 →L[ℝ] V3 →L[ℝ] ℝ

local instance : NormedAddCommGroup (V3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Bil3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Bil3) := ContinuousLinearMap.toNormedSpace

theorem metricLimit_pullback_scalar_seq
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier}
    {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hlim : SurgeryMetricLimitOn A B g gT f U T)
    {h : V3 → A.carrier} {W : Set V3} (hW : IsOpen W)
    (hh : ContMDiffOn (𝓡 3) (𝓡 3) ∞ h W) (hhU : MapsTo h W U)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[<] T))
    (m : ℕ) {K : Set V3} (hK : IsCompact K) (hKW : K ⊆ W)
    (a b : Fin 3) :
    TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (surgeryMetricCoefficient (g (t i)) h a b))
      (iteratedFDeriv ℝ m (surgeryMetricCoefficient gT (f ∘ h) a b)) atTop K := by
  let L : (Bil3) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
      (ContinuousLinearMap.apply ℝ (V3 →L[ℝ] ℝ)
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
  have hfh : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f ∘ h) W := hf.comp hh hhU
  have hB₀ : ContDiffOn ℝ ∞ (gT.pullbackCoefficients (f ∘ h)) W := by
    intro x hx
    exact (gT.contDiffAt_pullbackCoefficients
      (hfh.contMDiffAt (hW.mem_nhds hx))).contDiffWithinAt
  have hBlocal : ∀ x ∈ W, ∃ V, IsOpen V ∧ x ∈ V ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ ((g (t i)).pullbackCoefficients h) V := by
    intro x hx
    refine ⟨W, hW, hx, Eventually.of_forall fun i y hy => ?_⟩
    exact ((g (t i)).contDiffAt_pullbackCoefficients
      (hh.contMDiffAt (hW.mem_nhds hy))).contDiffWithinAt
  have hjet := (smooth_convergence_continuousLinearMap_comp L hW hB₀ hBlocal
    (fun j C hC hCW => metricLimit_pullbackCoefficients_seq hU hf hlim hW hh hhU ht
      j hC hCW)).2 m K hK hKW
  exact hjet

private theorem uniform_left_norm_sub
    {X Y : Type*} [NormedAddCommGroup Y]
    {F : ℝ → X → Y} {F₀ : X → Y} {K : Set X} {T eta : ℝ}
    (hconv : TendstoUniformlyOn F F₀ (𝓝[<] T) K) (heta : 0 < eta) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, T - d < t → t < T → ∀ x ∈ K,
      ‖F t x - F₀ x‖ < eta := by
  have hbound := Metric.tendstoUniformlyOn_iff.mp hconv eta heta
  obtain ⟨s, hs, hsbound⟩ := (nhdsLT_basis T).mem_iff.mp hbound
  refine ⟨T - s, sub_pos.mpr hs, ?_⟩
  intro t ht hT x hx
  have ht' : t ∈ Ioo s T := ⟨by linarith, hT⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hsbound ht' x hx

theorem surgeryMetricLimitOn_pullback_source
    {A B C : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier}
    {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hlim : SurgeryMetricLimitOn A B g gT f U T)
    (e : Diffeomorph (𝓡 3) (𝓡 3) C.carrier A.carrier ∞) :
    SurgeryMetricLimitOn C B
      (fun t => (g t).pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph)
      gT (f ∘ e) (e ⁻¹' U) T := by
  intro q hq K hK htarget hKU m a b eta heta
  let c := extChartAt (𝓡 3) q
  let W := chartRegularDomain C q (e ⁻¹' U)
  let h := e ∘ c.symm
  have hW : IsOpen W := chartRegularDomain_open C q (hU.preimage e.continuous)
  have hh : ContMDiffOn (𝓡 3) (𝓡 3) ∞ h W :=
    e.contMDiff.comp_contMDiffOn ((contMDiffOn_extChartAt_symm q).mono inter_subset_left)
  have hhU : MapsTo h W U := fun _ hx => hx.2
  have hKW : K ⊆ W := by
    intro x hx
    exact ⟨htarget hx, hKU ⟨x, hx, rfl⟩⟩
  have hconv : TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ m (singularMetricCoefficient
        ((g t).pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph) q a b))
      (iteratedFDeriv ℝ m
        (surgeryMetricCoefficient gT (fun z => f (e (c.symm z))) a b)) (𝓝[<] T) K := by
    apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
    intro t ht
    have hseq := metricLimit_pullback_scalar_seq hU hf hlim hW hh hhU ht m hK hKW a b
    apply hseq.congr
    refine Eventually.of_forall fun i x hx => ?_
    have heq : EqOn (surgeryMetricCoefficient (g (t i)) h a b)
        (singularMetricCoefficient
          ((g (t i)).pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph) q a b) W := by
      intro y hy
      exact (M51.singularMetricCoefficient_pullback (g (t i)) e q a b hy.1).symm
    exact eqOn_iteratedFDeriv_of_isOpen hW heq m (hKW hx)
  exact uniform_left_norm_sub hconv heta

theorem MetricLimitTransportData.of_source
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice slice' : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T)
    (p : Diffeomorph (𝓡 3) (𝓡 3)
      (slice E.tMinus).carrier (slice' E.tMinus).carrier ∞) :
    MetricLimitTransportData E p where
  metric_converges := surgeryMetricLimitOn_pullback_source E.regular_limit_open
    E.limit_identify.map_smooth E.metric_converges p.symm

end PoincareConjecture.M51EventTransport
