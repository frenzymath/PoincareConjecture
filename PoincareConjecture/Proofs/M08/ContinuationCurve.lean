import PoincareConjecture.Proofs.M08.ContinuationLocalODE
import PoincareConjecture.Proofs.M08.EulerPathCharts
import PoincareConjecture.Proofs.M08.ChartEulerEquation
import PoincareConjecture.Proofs.M08.GlobalCurveExtension
import PoincareConjecture.Proofs.M08.ReferenceEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance continuationCurveDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance continuationCurveDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance continuationCurveBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance continuationCurveBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def continuationCurvePhase {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)
    (α : ℝ → M) (s : ℝ) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let q := (extChartAt (𝓡 n) x) ∘ α
  (q s, chartMetricOperator F T x (s, q s) (deriv q s))

theorem continuationCurvePhase_rhs {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (α : ℝ → M) {s : ℝ}
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    closedChartEulerPhase F T x univ s (continuationCurvePhase F T x α s) =
      (deriv ((extChartAt (𝓡 n) x) ∘ α) s,
        chartForceVector
          (spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (α s)))
          (spatialFDeriv (chartActionPotential F T x) (s, extChartAt (𝓡 n) x (α s)))
          (deriv ((extChartAt (𝓡 n) x) ∘ α) s)) := by
  let q := (extChartAt (𝓡 n) x) ∘ α
  have htarget : q s ∈ (extChartAt (𝓡 n) x).target :=
    (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hx)
  change closedChartEulerPhase F T x univ s
    (q s, chartMetricOperator F T x (s, q s) (deriv q s)) = _
  dsimp only [closedChartEulerPhase]
  rw [inverse_operator_apply _ (chartMetricOperator_isUnit_of_target F T x htarget)]
  rw [spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
      _ univ_mem htarget,
    spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
      _ univ_mem htarget]
  rfl

structure IsContinuationCurve {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (U : Set ℝ) : Prop where
  smooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U
  phase : ∀ s ∈ U, ∀ x : M,
    α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source →
    HasDerivAt (continuationCurvePhase F T x α)
      (closedChartEulerPhase F T x univ s (continuationCurvePhase F T x α s)) s

theorem IsContinuationCurve.mono {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {α : ℝ → M} {U V : Set ℝ} (hα : IsContinuationCurve F T α U) (hVU : V ⊆ U) :
    IsContinuationCurve F T α V :=
  ⟨hα.smooth.mono hVU, fun s hs ↦ hα.phase s (hVU hs)⟩

theorem IsContinuationCurve.union {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {α : ℝ → M} {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (hαU : IsContinuationCurve F T α U) (hαV : IsContinuationCurve F T α V) :
    IsContinuationCurve F T α (U ∪ V) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases hs with hs | hs
    · exact ((hαU.smooth s hs).contMDiffAt (hU.mem_nhds hs)).contMDiffWithinAt
    · exact ((hαV.smooth s hs).contMDiffAt (hV.mem_nhds hs)).contMDiffWithinAt
  · intro s hs
    rcases hs with hs | hs
    · exact hαU.phase s hs
    · exact hαV.phase s hs

theorem continuationCurvePhase_eventuallyEq {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) {α β : ℝ → M} {s : ℝ} (h : α =ᶠ[𝓝 s] β) :
    continuationCurvePhase F T x α =ᶠ[𝓝 s] continuationCurvePhase F T x β := by
  have hq : (extChartAt (𝓡 n) x ∘ α) =ᶠ[𝓝 s] (extChartAt (𝓡 n) x ∘ β) :=
    h.fun_comp (extChartAt (𝓡 n) x)
  filter_upwards [hq, hq.deriv] with r hr hdr
  simp only [continuationCurvePhase, hr, hdr]

theorem IsContinuationCurve.congr {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {α β : ℝ → M} {U : Set ℝ} (hU : IsOpen U) (hα : IsContinuationCurve F T α U)
    (heq : EqOn β α U) : IsContinuationCurve F T β U := by
  refine ⟨hα.smooth.congr heq, ?_⟩
  intro s hs x hx
  have hnear : β =ᶠ[𝓝 s] α := Filter.eventuallyEq_of_mem (hU.mem_nhds hs) heq
  have hp := continuationCurvePhase_eventuallyEq F T x hnear
  have h := hα.phase s hs x (by simpa only [heq hs] using hx)
  rw [← hp.self_of_nhds] at h
  exact h.congr_of_eventuallyEq hp

theorem continuationChartPhase_contDiffOn {J U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) (hU : IsOpen U)
    (htime : ∀ s ∈ U, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (Function.uncurry (closedChartEulerPhase F T x univ))
      (U ×ˢ ((extChartAt (𝓡 n) x).target ×ˢ univ)) := by
  apply (closedChartEulerPhase_contDiffOn F hM04 T x hU.uniqueDiffOn htime).congr
  intro z hz
  unfold Function.uncurry closedChartEulerPhase
  rw [spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
      _ univ_mem hz.2.1,
    spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
      _ univ_mem hz.2.1,
    spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
      _ (hU.mem_nhds hz.1) hz.2.1,
    spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x)
      _ (hU.mem_nhds hz.1) hz.2.1]

theorem closedChartEulerPhase_eq_univ {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C)
    (ht : T - s ^ 2 ∈ interior J)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (hz : z.1 ∈ (extChartAt (𝓡 n) x).target) :
    closedChartEulerPhase F T x C s z = closedChartEulerPhase F T x univ s z := by
  have hG := (hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x)
    (chartActionMetric F T x) (chartActionMetric_closed_contDiffOn F T x htime) hs hz).unique
    (hasFDerivAt_spatial (chartActionDomain_open F T x) _
      (chartActionMetric_contDiffOn F T x) ⟨ht, hz⟩)
  have hV := (hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x)
    (chartActionPotential F T x) (chartActionPotential_closed_contDiffOn F hM04 T x htime) hs hz).unique
    (hasFDerivAt_spatial (chartActionDomain_open F T x) _
      (chartActionPotential_contDiffOn F hM04 T x) ⟨ht, hz⟩)
  unfold closedChartEulerPhase
  rw [hG, hV,
    spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x) _ univ_mem hz,
    spatialWithinFDeriv_eq_spatialFDeriv (isOpen_extChartAt_target (I := 𝓡 n) x) _ univ_mem hz]

set_option maxHeartbeats 1600000 in
theorem isContinuationCurve_of_regularizedEuler {J U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hU : IsOpen U) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (htime : ∀ s ∈ U, T - s ^ 2 ∈ interior J)
    (E : ParametricAlongCurveExtensionOn U α (curveVelocityWithin (n := n) α U))
    (hE : ∀ s ∈ U, regularizedLGeodesicEquation F T α U E s) :
    IsContinuationCurve F T α U := by
  refine ⟨hα, ?_⟩
  intro s hs x hx
  let N := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hN : IsOpen N := hα.continuousOn.isOpen_inter_preimage hU
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hNU : N ⊆ U := inter_subset_left
  have hsN : s ∈ N := ⟨hs, hx⟩
  have hsrc : MapsTo α N (chartAt (EuclideanSpace ℝ (Fin n)) x).source := fun _ hr ↦ hr.2
  let E' := restrictOpenVelocityExtension hU hN hNU α E
  have heuler : regularizedLGeodesicEquation F T α N E' s := by
    intro W
    rw [regularizedEulerResidual_restrictOpenVelocityExtension F T hU hN hNU α E hsN W]
    exact hE s hs W
  have hmomentum := regularized_equation_chart_momentum F hM04 T hN x α
    ((hα.mono hNU).of_le (by simp)) hsrc E' hsN (htime s hs) heuler
  let q := (extChartAt (𝓡 n) x) ∘ α
  have hqd : HasDerivAt q (deriv q s) s :=
    (((chart_curve_contDiffOn x α (hα.mono hNU) hsrc) s hsN).contDiffAt
      (hN.mem_nhds hsN)).differentiableAt (by simp) |>.hasDerivAt
  rw [continuationCurvePhase_rhs F T x α hx]
  exact hqd.prodMk hmomentum

set_option maxHeartbeats 1000000 in
theorem continuationCurve_momentum {J U : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {α : ℝ → M} (hα : IsContinuationCurve F T α U) {s : ℝ} (hs : s ∈ U)
    (x : M) (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    HasDerivAt (fun r ↦ chartMomentumVector
        (chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) r))
      (chartForceVector
        (spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (α s)))
        (spatialFDeriv (chartActionPotential F T x) (s, extChartAt (𝓡 n) x (α s)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) s)) s := by
  have h : HasDerivAt (fun r ↦ (continuationCurvePhase F T x α r).2)
      (closedChartEulerPhase F T x univ s (continuationCurvePhase F T x α s)).2 s :=
    (hα.phase s hs x hx).snd
  rw [continuationCurvePhase_rhs F T x α hx] at h
  exact h

theorem continuationCurve_regularizedEuler {J U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hU : IsOpen U)
    {α : ℝ → M} (hα : IsContinuationCurve F T α U)
    (htime : ∀ s ∈ U, T - s ^ 2 ∈ interior J) :
    ∃ E : ParametricAlongCurveExtensionOn U α (curveVelocityWithin (n := n) α U),
      ∀ s ∈ U, regularizedLGeodesicEquation F T α U E s := by
  apply exists_regularizedEuler_extension_of_local F T hU α
  intro s hs
  let x := α s
  let N := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hN : IsOpen N := hα.smooth.continuousOn.isOpen_inter_preimage hU
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hNU : N ⊆ U := inter_subset_left
  have hsrc : MapsTo α N (chartAt (EuclideanSpace ℝ (Fin n)) x).source := fun _ hr ↦ hr.2
  refine ⟨N, hN, ⟨hs, mem_chart_source _ _⟩, hNU,
    chartVelocityExtension hN x α (hα.smooth.mono hNU) hsrc, ?_⟩
  intro r hr
  exact chart_momentum_regularized_equation F hM04 T hN x α
    (hα.smooth.mono hNU) hsrc hr (htime r hr.1)
    (continuationCurve_momentum F T hα hr.1 x hr.2)

set_option maxHeartbeats 1800000 in
theorem exists_continuationCurve_from_phase {J U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) (hU : IsOpen U)
    (htime : ∀ s ∈ U, T - s ^ 2 ∈ interior J) {s : ℝ} (hs : s ∈ U)
    (q₀ P₀ : EuclideanSpace ℝ (Fin n)) (hq₀ : q₀ ∈ (extChartAt (𝓡 n) x).target) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ α : ℝ → M,
      Ioo (s - 2 * ε) (s + 2 * ε) ⊆ U ∧
      IsContinuationCurve F T α (Ioo (s - 2 * ε) (s + 2 * ε)) ∧
      continuationCurvePhase F T x α s = (q₀, P₀) ∧
      MapsTo α (Ioo (s - 2 * ε) (s + 2 * ε))
        (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
  let e := extChartAt (𝓡 n) x
  obtain ⟨ε, hε, z, hz₀, hWU, hzT, hzs, hzd⟩ := exists_smooth_local_phase hU
    ((isOpen_extChartAt_target (I := 𝓡 n) x).prod isOpen_univ)
    (closedChartEulerPhase F T x univ)
    (continuationChartPhase_contDiffOn F hM04 T x hU (fun r hr ↦ interior_subset (htime r hr)))
    hs (show (q₀, P₀) ∈ e.target ×ˢ univ from ⟨hq₀, mem_univ _⟩)
  let W := Ioo (s - 2 * ε) (s + 2 * ε)
  let q := fun r ↦ (z r).1
  let α := e.symm ∘ q
  have hW : IsOpen W := isOpen_Ioo
  have hsW : s ∈ W := ⟨by linarith, by linarith⟩
  have hqT : MapsTo q W e.target := fun r hr ↦ (hzT hr).1
  have hαs : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α W :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp hzs.fst.contMDiffOn hqT
  have hsrc : MapsTo α W (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    intro r hr
    simpa only [α, Function.comp_apply, e, extChartAt_source] using e.map_target (hqT hr)
  have hqeq : EqOn (e ∘ α) q W := fun r hr ↦ e.right_inv (hqT hr)
  have hphase (r : ℝ) (hr : r ∈ W) : continuationCurvePhase F T x α r = z r := by
    have hfirst : HasDerivAt q
        (Ring.inverse (chartMetricOperator F T x (r, q r)) (z r).2) r := (hzd r hr).fst
    have hdiff : deriv (e ∘ α) r = deriv q r :=
      (Filter.eventuallyEq_of_mem (hW.mem_nhds hr) hqeq).deriv_eq
    apply Prod.ext
    · exact hqeq hr
    · change chartMetricOperator F T x (r, e (α r)) (deriv (e ∘ α) r) = (z r).2
      rw [show e (α r) = q r from hqeq hr, hdiff, hfirst.deriv]
      exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ A (z r).2)
        (Ring.mul_inverse_cancel _ (chartMetricOperator_isUnit_of_target F T x (hqT hr)))
  let E := chartVelocityExtension hW x α hαs hsrc
  have hEuler (r : ℝ) (hr : r ∈ W) : regularizedLGeodesicEquation F T α W E r := by
    have hnear : continuationCurvePhase F T x α =ᶠ[𝓝 r] z :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hr) hphase
    have hp : HasDerivAt (continuationCurvePhase F T x α)
        (closedChartEulerPhase F T x univ r (continuationCurvePhase F T x α r)) r := by
      rw [hphase r hr]
      exact (hzd r hr).congr_of_eventuallyEq hnear
    have hm : HasDerivAt (fun t ↦ (continuationCurvePhase F T x α t).2)
        (closedChartEulerPhase F T x univ r (continuationCurvePhase F T x α r)).2 r := hp.snd
    have hm' : HasDerivAt (fun t ↦ chartMomentumVector
          (chartActionMetric F T x (t, e (α t))) (deriv (e ∘ α) t))
        (chartForceVector
          (spatialFDeriv (chartActionMetric F T x) (r, e (α r)))
          (spatialFDeriv (chartActionPotential F T x) (r, e (α r)))
          (deriv (e ∘ α) r)) r := by
      rw [continuationCurvePhase_rhs F T x α (hsrc hr)] at hm
      exact hm
    exact chart_momentum_regularized_equation F hM04 T hW x α hαs hsrc hr
      (htime r (hWU hr)) hm'
  exact ⟨ε, hε, α, hWU,
    isContinuationCurve_of_regularizedEuler F hM04 T hW α hαs
      (fun r hr ↦ htime r (hWU hr)) E hEuler, (hphase s hsW).trans hz₀, hsrc⟩

set_option maxHeartbeats 1000000 in
theorem continuationCurve_eventuallyEq_of_phase_eq {J U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, T - s ^ 2 ∈ J) {α β : ℝ → M}
    (hα : IsContinuationCurve F T α U) (hβ : IsContinuationCurve F T β U)
    {s : ℝ} (hs : s ∈ U) (x : M)
    (hαx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hβx : β s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (heq : continuationCurvePhase F T x α s = continuationCurvePhase F T x β s) :
    α =ᶠ[𝓝 s] β := by
  let e := extChartAt (𝓡 n) x
  let z := continuationCurvePhase F T x α
  let w := continuationCurvePhase F T x β
  have htarget : (z s).1 ∈ e.target := e.map_source (by
    simpa only [e, extChartAt_source] using hαx)
  have hdom : (s, z s) ∈ U ×ˢ (e.target ×ˢ univ) := ⟨hs, htarget, mem_univ _⟩
  have hfield : ContDiffAt ℝ 1
      (Function.uncurry (closedChartEulerPhase F T x univ)) (s, z s) :=
    (((continuationChartPhase_contDiffOn F hM04 T x hU htime) _ hdom).contDiffAt
      ((hU.prod ((isOpen_extChartAt_target (I := 𝓡 n) x).prod isOpen_univ)).mem_nhds
        hdom)).of_le (by simp)
  have hαc := ((hα.smooth s hs).contMDiffAt (hU.mem_nhds hs)).continuousAt
  have hβc := ((hβ.smooth s hs).contMDiffAt (hU.mem_nhds hs)).continuousAt
  have hαnear := hαc ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hαx)
  have hβnear := hβc ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hβx)
  have hz : ∀ᶠ r in 𝓝 s, HasDerivAt z (closedChartEulerPhase F T x univ r (z r)) r := by
    filter_upwards [hU.mem_nhds hs, hαnear] with r hr hx
    exact hα.phase r hr x hx
  have hw : ∀ᶠ r in 𝓝 s, HasDerivAt w (closedChartEulerPhase F T x univ r (w r)) r := by
    filter_upwards [hU.mem_nhds hs, hβnear] with r hr hx
    exact hβ.phase r hr x hx
  have hphase := smooth_phase_eventuallyEq _ hfield hz hw heq
  filter_upwards [hphase, hαnear, hβnear] with r hr hαr hβr
  have hq : e (α r) = e (β r) := congrArg Prod.fst hr
  have hαr' : α r ∈ e.source := by
    simpa only [e, extChartAt_source] using
      (show α r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source from hαr)
  have hβr' : β r ∈ e.source := by
    simpa only [e, extChartAt_source] using
      (show β r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source from hβr)
  calc
    α r = e.symm (e (α r)) := (e.left_inv hαr').symm
    _ = e.symm (e (β r)) := congrArg e.symm hq
    _ = β r := e.left_inv hβr'

set_option maxHeartbeats 1000000 in
theorem continuationCurve_eqOn_of_germ [T2Space M] {J U : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    (hU : IsOpen U) (hUc : IsPreconnected U) (htime : ∀ s ∈ U, T - s ^ 2 ∈ J)
    {α β : ℝ → M} (hα : IsContinuationCurve F T α U) (hβ : IsContinuationCurve F T β U)
    {s : ℝ} (hs : s ∈ U) (hseed : α =ᶠ[𝓝 s] β) : EqOn α β U := by
  let S := {r : ℝ | α =ᶠ[𝓝 r] β}
  have hS : IsOpen S := isOpen_setOf_eventually_nhds
  have hcl : closure S ∩ U ⊆ S := by
    intro r hr
    haveI : NeBot (𝓝[S] r) := mem_closure_iff_nhdsWithin_neBot.mp hr.1
    have hαc := ((hα.smooth r hr.2).contMDiffAt (hU.mem_nhds hr.2)).continuousAt
    have hβc := ((hβ.smooth r hr.2).contMDiffAt (hU.mem_nhds hr.2)).continuousAt
    have hbaseNear : α =ᶠ[𝓝[S] r] β := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ht.self_of_nhds
    have hbase : α r = β r := tendsto_nhds_unique
      ((hαc.tendsto.mono_left nhdsWithin_le_nhds).congr' hbaseNear)
      (hβc.tendsto.mono_left nhdsWithin_le_nhds)
    let x := α r
    have hxα : α r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ _
    have hxβ : β r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by rwa [← hbase]
    have hpNear : continuationCurvePhase F T x α =ᶠ[𝓝[S] r]
        continuationCurvePhase F T x β := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (continuationCurvePhase_eventuallyEq F T x ht).self_of_nhds
    have hp : continuationCurvePhase F T x α r = continuationCurvePhase F T x β r :=
      tendsto_nhds_unique
        (((hα.phase r hr.2 x hxα).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hpNear)
        ((hβ.phase r hr.2 x hxβ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    exact continuationCurve_eventuallyEq_of_phase_eq F hM04 T hU htime hα hβ hr.2 x hxα hxβ hp
  have hUS : U ⊆ S := hUc.subset_of_closure_inter_subset hS ⟨s, hs, hseed⟩ hcl
  exact fun r hr ↦ (hUS hr).self_of_nhds

end PoincareConjecture.M08
