import PoincareConjecture.Proofs.M08.MinimizerEulerLocal
import PoincareConjecture.Proofs.M08.ChartEulerRegularity
import PoincareConjecture.Proofs.M08.ChartEulerEquation
import PoincareConjecture.Proofs.M08.GlobalCurveExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [mTop : TopologicalSpace M]
  [mChart : ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [mSmooth : IsManifold (𝓡 n) ∞ M] [mConnected : ConnectedSpace M] [mT3 : T3Space M]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem isBackwardLGeodesic_of_minimizing {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₂ : τ₂ ≤ τmax) (p : BackwardTimePath F T τ₁ τ₂)
    (hp : IsMinimizingBackwardLPath F T τ₁ τ₂ p) : IsBackwardLGeodesic F T τ₁ τ₂ p := by
  letI : MetricSpace M := referenceMetricSpace (F.metric T)
  let α := squareReparameterizedCurve p.curve
  have hloc : ∀ s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂), ∃ U : Set ℝ,
      IsOpen U ∧ s ∈ U ∧ U ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ∧
      ∃ E : ParametricAlongCurveExtensionOn U α (curveVelocityWithin (n := n) α U),
        ∀ r ∈ U, regularizedLGeodesicEquation F T α U E r := by
    intro s hs
    obtain ⟨a, b, x, w, hAa, has, hsb, hbB, hsrc, hw, hmin⟩ :=
      @minimizing_squarePath_local_minimum n M mTop mChart mSmooth mConnected mT3
        J F T τmax τ₁ τ₂ s hM04 hwindow hcurvature hτ₂ p hp hs
    have hsub : Icc a b ⊆ Icc (Real.sqrt τ₁) (Real.sqrt τ₂) :=
      Icc_subset_Icc hAa.le hbB.le
    have htime (r : ℝ) (hr : r ∈ Icc a b) : T - r ^ 2 ∈ interior J :=
      backwardSquareTime_mem_interior hwindow p.nonnegative p.ordered hτ₂
        ⟨hAa.trans_le hr.1, hr.2.trans_lt hbB⟩
    obtain ⟨hsm, hmom⟩ := chart_minimum_smooth_momentum F hM04 T (has.trans hsb) x α
      ((squarePath_continuousOn p).mono hsub) hsrc htime w hw hmin
    let e := extChartAt (𝓡 n) x
    have hsrc' : MapsTo α (Icc a b) e.source := by
      simpa only [e, extChartAt_source] using hsrc
    have htarget : MapsTo (e ∘ α) (Icc a b) e.target :=
      fun r hr ↦ e.map_source (hsrc' hr)
    have hcomp := (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp hsm.contMDiffOn htarget
    have hαcc : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (Icc a b) :=
      hcomp.congr (fun r hr ↦ (e.left_inv (hsrc' hr)).symm)
    have hα := hαcc.mono Ioo_subset_Icc_self
    have hsrcU := hsrc.mono_left Ioo_subset_Icc_self
    refine ⟨Ioo a b, isOpen_Ioo, ⟨has, hsb⟩, Ioo_subset_Ioo hAa.le hbB.le,
      chartVelocityExtension isOpen_Ioo x α hα hsrcU, ?_⟩
    intro r hr
    exact chart_momentum_regularized_equation F hM04 T isOpen_Ioo x α hα hsrcU hr
      (htime r (Ioo_subset_Icc_self hr)) (hmom r hr)
  obtain ⟨E, heq⟩ := exists_regularizedEuler_extension_of_local F T isOpen_Ioo α hloc
  exact isBackwardLGeodesic_of_regularizedEuler_extension hM04 p E heq

end PoincareConjecture.M08
