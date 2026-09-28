import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.NormalizedKappaSpacetimeEmbedding

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalEmbeddingCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {kappa : ℝ} {source target : BasedKappaSolution kappa}
  {U : Set target.carrier.carrier}
  (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target)
    (Iic 0 ×ˢ U))

theorem contMDiffOn_terminalSpatialMap {t : ℝ} (ht : t ≤ 0) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => (e.toFun (t, x)).2) U := by
  exact contMDiff_snd.comp_contMDiffOn
    (e.smooth_on.comp (contMDiffOn_const.prodMk contMDiffOn_id)
      (fun x hx => ⟨ht, hx⟩))

theorem terminal_coefficient_eq_fixed_pullback
    (hU : IsOpen U)
    (hfixed : ∀ s t : ℝ, ∀ x ∈ U, s ≤ 0 → t ≤ 0 →
      (e.toFun (s, x)).2 = (e.toFun (t, x)).2)
    (q : target.carrier.carrier) (a b : Fin 3) {t : ℝ} (ht : t ≤ 0)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hxU : (extChartAt (𝓡 3) q).symm x ∈ U) :
    normalizedKappaPullbackCoefficient e q a b (t, x) =
      (source.flow.flow.metric t).pullbackCoefficients
        ((fun y => (e.toFun (0, y)).2) ∘ (extChartAt (𝓡 3) q).symm) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  let ψ := fun y => (e.toFun (0, y)).2
  have heq : (fun y => (e.toFun (t, y)).2) =ᶠ[𝓝 ((extChartAt (𝓡 3) q).symm x)] ψ :=
    Filter.eventually_of_mem (hU.mem_nhds hxU) (fun y hy => hfixed t 0 y hy ht le_rfl)
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx).contMDiffAt
    (extChartAt_target_mem_nhds' hx)
  have he := (e.contMDiffOn_terminalSpatialMap (t := 0) le_rfl).contMDiffAt
    (hU.mem_nhds hxU)
  have hd : mfderiv (𝓡 3) (𝓡 3) (ψ ∘ (extChartAt (𝓡 3) q).symm) x =
      (mfderiv (𝓡 3) (𝓡 3) ψ ((extChartAt (𝓡 3) q).symm x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm x) :=
    mfderiv_comp x (he.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  unfold normalizedKappaPullbackCoefficient normalizedKappaPullbackInnerValue
  dsimp only
  rw [heq.eq_of_nhds, heq.mfderiv_eq]
  unfold RiemannianMetric.pullbackCoefficients
  erw [hd]
  rfl

theorem contDiffOn_terminalCoefficient
    (hU : IsOpen U)
    (hfixed : ∀ s t : ℝ, ∀ x ∈ U, s ≤ 0 → t ≤ 0 →
      (e.toFun (s, x)).2 = (e.toFun (t, x)).2)
    (q : target.carrier.carrier) (a b : Fin 3) :
    ContDiffOn ℝ ∞ (normalizedKappaPullbackCoefficient e q a b)
      (Iic 0 ×ˢ ((extChartAt (𝓡 3) q).target ∩
        (extChartAt (𝓡 3) q).symm ⁻¹' U)) := by
  let V := (extChartAt (𝓡 3) q).target ∩ (extChartAt (𝓡 3) q).symm ⁻¹' U
  have hV : IsOpen V :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) hU
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      ((fun y => (e.toFun (0, y)).2) ∘ (extChartAt (𝓡 3) q).symm) V :=
    (e.contMDiffOn_terminalSpatialMap (t := 0) le_rfl).comp
      ((contMDiffOn_extChartAt_symm (n := ∞) q).mono inter_subset_left)
      (fun x hx => hx.2)
  have hs := (source.flow.flow.contDiffOn_pullbackCoefficients_within hV he)
    |>.clm_apply (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))
    |>.clm_apply (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
  apply hs.congr
  intro p hp
  exact e.terminal_coefficient_eq_fixed_pullback hU hfixed q a b hp.1 hp.2.1 hp.2.2

end PoincareConjecture.NormalizedKappaSpacetimeEmbedding
