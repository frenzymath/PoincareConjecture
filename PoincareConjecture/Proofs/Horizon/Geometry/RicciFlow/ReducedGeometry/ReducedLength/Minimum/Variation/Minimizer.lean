import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Endpoint
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.MinimizingCurve
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Extension.Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational
open ReducedLengthMinimum.Variation ReducedLengthMinimum.Variation.Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

set_option maxHeartbeats 1600000 in

theorem exists_spatial_minimizing_sqrtRegularPath (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ q : BackwardTimePath K.flow 0 0 τ, ∃ S : SqrtRegularPath q,
      ∃ E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve
        (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ))),
      q.curve 0 = p ∧
      backwardLLength K.flow 0 0 τ q.curve =
        2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ ∧
      (∀ r : BackwardTimePath K.flow 0 0 τ, r.curve 0 = p →
        backwardLLength K.flow 0 0 τ q.curve ≤ backwardLLength K.flow 0 0 τ r.curve) ∧
      (∀ s ∈ Ioo 0 (Real.sqrt τ),
        regularizedLGeodesicEquation K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) E s) ∧
      curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0 := by
  let : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
  let : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 2)
  have hc : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  obtain ⟨paths, γ, _, hanti, haction, hγ, hγ0, hlim, _⟩ :=
    K.exists_spatial_minimizing_uniform_limit p hτ
  have hreg := K.minimizing_uniform_limit_contMDiffOn_Icc
    p hτ paths hanti haction γ hγ hγ0 hlim
  obtain ⟨α, U, hU, hIU, hα, hαγ⟩ := exists_smooth_manifold_extension_Icc hc γ hreg
  obtain ⟨m, t, x, Q, _, ht, hta, htb, hQ, _⟩ :=
    exists_compact_partition_of_uniform_limit
      (fun x : M => (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
      (fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source)
      (fun y => ⟨y, mem_chart_source _ y⟩) hc.le γ hγ
      (fun k s => (paths k).curve (s ^ 2)) hlim
  obtain ⟨w, hw, hsum⟩ := K.finite_chart_limit_le_spatialInfimum p hτ paths hanti
    haction γ hγ hlim t ht hta htb x Q hQ
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source :=
    fun s hs => (hQ i).2.2 (interior_subset ((hQ i).2.1 (mem_image_of_mem γ hs)))
  obtain ⟨q, hq, hact, hminimal⟩ := K.exists_minimizing_path_of_regular_chart_limit hτ
    t ht hta htb γ hγ.continuousOn
    ((hreg.mono Ioo_subset_Icc_self).of_le (by simp)) x hsrc w hw
    (by simpa only [chartH1Action, hγ0] using hsum)
  have hq0 : q.curve 0 = γ 0 := by simpa only [Real.sqrt_zero] using hq 0
  have hagrees (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt τ)) : α s = q.curve (s ^ 2) := by
    rw [hq, Real.sqrt_sq hs.1]
    exact hαγ hs
  let S : SqrtRegularPath q := {
    curve := α
    domain := U
    open_domain := hU
    interval_subset := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hIU
    smooth := hα
    agrees := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hagrees }
  obtain ⟨E⟩ := exists_parametricVelocityExtension hU hIU (uniqueDiffOn_Icc hc) α hα
  have hminimal' (r : BackwardTimePath K.flow 0 0 τ) (hr : r.curve 0 = q.curve 0) :
      backwardLLength K.flow 0 0 τ q.curve ≤ backwardLLength K.flow 0 0 τ r.curve :=
    hminimal r (hr.trans hq0)
  have hterminal := K.minimizing_uniform_limit_terminal_velocity_eq_zero
    p hτ paths hanti haction γ hγ hγ0 hlim q hminimal' α U hU hIU hα hαγ hagrees
  refine ⟨q, S, E, hq0.trans hγ0, ?_, ?_, ?_, hterminal⟩
  · simpa only [hγ0] using hact
  · intro r hr
    exact hminimal r (hr.trans hγ0.symm)
  · intro s hs W
    have hsC : s ∈ Icc 0 (Real.sqrt τ) := Ioo_subset_Icc_self hs
    let Eγ := transferParametricExtension hαγ
      (fun r hr ↦ curveVelocityWithin_congr hαγ hr) E
    have heuler := K.minimizing_uniform_limit_regularizedLGeodesicEquation
      p hτ paths hanti haction γ hγ hγ0 hlim Eγ hs W
    have hαs := ((hα s (hIU hsC)).contMDiffAt (hU.mem_nhds (hIU hsC))).mdifferentiableAt
      (by simp)
    have hcongr := regularizedEulerResidual_congr K.flow 0 hαγ.symm Eγ E hsC
      (uniqueDiffOn_Icc hc s hsC) hαs W
    rw [hcongr] at heuler
    exact heuler

end PoincareConjecture.AncientKappaSolution
