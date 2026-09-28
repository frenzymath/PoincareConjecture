import PoincareConjecture.Proofs.M51.EventTransportMetricCharts












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



theorem metricLimit_pullbackCoefficients_seq
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier}
    {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hlim : SurgeryMetricLimitOn A B g gT f U T)
    {h : V3 → A.carrier} {W : Set V3} (hW : IsOpen W)
    (hh : ContMDiffOn (𝓡 3) (𝓡 3) ∞ h W) (hhU : MapsTo h W U)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[<] T))
    (m : ℕ) {K : Set V3} (hK : IsCompact K) (hKW : K ⊆ W) :
    TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m ((g (t i)).pullbackCoefficients h))
      (iteratedFDeriv ℝ m (gT.pullbackCoefficients (f ∘ h))) atTop K := by
  apply tendstoUniformlyOn_iteratedFDeriv_of_local_models hW ?_ m hK hKW
  intro z hz
  let q := h z
  let c := extChartAt (𝓡 3) q
  let O := chartRegularDomain A q U
  let V := W ∩ h ⁻¹' c.source
  let a := c ∘ h
  let S : ℕ → V3 → Bil3 := fun i => (g (t i)).pullbackCoefficients c.symm
  let S₀ : V3 → Bil3 := gT.pullbackCoefficients (f ∘ c.symm)
  have hO : IsOpen O := chartRegularDomain_open A q hU
  have hV : IsOpen V := hh.continuousOn.isOpen_inter_preimage hW
    (isOpen_extChartAt_source q)
  have hzV : z ∈ V := ⟨hz, mem_extChartAt_source q⟩
  have hhh : ContMDiffOn (𝓡 3) (𝓡 3) ∞ h V := hh.mono inter_subset_left
  have ha : ContDiffOn ℝ ∞ a V := contMDiffOn_iff_contDiffOn.mp
    ((contMDiffOn_extChartAt (I := 𝓡 3) (x := q)).comp hhh
      (fun _ hy => by simpa only [c, extChartAt_source] using hy.2))
  have haO : MapsTo a V O := by
    intro y hy
    refine ⟨c.map_source hy.2, ?_⟩
    change c.symm (c (h y)) ∈ U
    rw [c.left_inv hy.2]
    exact hhU hy.1
  have hS₀ : ContDiffOn ℝ ∞ S₀ O := terminal_chart_contDiffOn gT hU hf q
  have hSlocal : ∀ x ∈ O, ∃ R, IsOpen R ∧ x ∈ R ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (S i) R := by
    intro x hx
    exact ⟨O, hO, hx, Eventually.of_forall fun i =>
      ((g (t i)).contDiffOn_chartCoefficients q).mono inter_subset_left⟩
  have hajet : ∀ j C, IsCompact C → C ⊆ V → TendstoUniformlyOn
      (fun _ : ℕ => iteratedFDeriv ℝ j a) (iteratedFDeriv ℝ j a) atTop C := by
    intro j C _ _
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro eta heta
    exact Eventually.of_forall fun _ _ _ => by simpa using heta
  obtain ⟨_, hjet⟩ := smooth_convergence_pullback_bilinear_on_open hO hV hS₀ ha haO
    hSlocal (fun x hx => ⟨V, hV, hx, Eventually.of_forall fun _ => ha⟩)
    (fun j C hC hCO => metricLimit_chart_jets_seq hU hf hlim q (hhU hz) ht j C hC hCO)
    hajet
  refine ⟨V, hV, hzV, inter_subset_left,
    (fun i y => (S i (a y)).bilinearComp (fderiv ℝ a y) (fderiv ℝ a y)),
    (fun y => (S₀ (a y)).bilinearComp (fderiv ℝ a y) (fderiv ℝ a y)),
    Eventually.of_forall ?_, ?_, hjet⟩
  · intro i y hy
    have hheq := chart_factor_eventuallyEq q
      (hhh.contMDiffAt (hV.mem_nhds hy)).continuousAt hy.2
    have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (a y) :=
      (contMDiffOn_extChartAt_symm q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (c.map_source hy.2))
    exact (pullbackCoefficients_congr (g (t i)) hheq.symm).trans
      (pullbackCoefficients_comp (g (t i)) hc (ha.contDiffAt (hV.mem_nhds hy)))
  · intro y hy
    have hheq := chart_factor_eventuallyEq q
      (hhh.contMDiffAt (hV.mem_nhds hy)).continuousAt hy.2
    have hfeq : ((f ∘ c.symm) ∘ a) =ᶠ[𝓝 y] (f ∘ h) := by
      filter_upwards [hheq] with w hw
      exact congrArg f hw
    have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (a y) :=
      (contMDiffOn_extChartAt_symm q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (c.map_source hy.2))
    have hcf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f ∘ c.symm) (a y) :=
      (hf.contMDiffAt (hU.mem_nhds (haO hy).2)).comp (a y) hc
    exact (pullbackCoefficients_congr gT hfeq.symm).trans
      (pullbackCoefficients_comp gT hcf (ha.contDiffAt (hV.mem_nhds hy)))

end PoincareConjecture.M51EventTransport
