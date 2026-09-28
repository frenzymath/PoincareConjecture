import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.Neighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.VectorField.Derivation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_uniform_coordinate_metric_jet_tail
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {q : M} (hq : q ∈ H.reference.regularLimitSet) :
    ∃ s r : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 < r ∧
      let c := extChartAt (𝓡 3) q
      Metric.closedBall (c q) r ⊆ c.target ∧
      c.symm '' Metric.closedBall (c q) r ⊆ H.reference.regularLimitSet ∧
      ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico s T,
        ∀ z ∈ Metric.closedBall (c q) r,
          ‖iteratedFDeriv ℝ m ((H.reference.flow.metric t).pullbackCoefficients c.symm) z‖ ≤ B := by
  obtain ⟨s, r, a, b, hs, hsT, hr, ha, hb, htarget, hreg, hell, hcurv⟩ :=
    H.exists_uniform_coordinate_neighborhood P04 hq
  let c := extChartAt (𝓡 3) q
  have hdom : (fun z : ℝ => z + s) '' Ioo (H.reference.tMinus - s) (T - s) ⊆
      Ico H.reference.tMinus T := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hzero : (0 : ℝ) ∈ Ioo (H.reference.tMinus - s) (T - s) :=
    ⟨by linarith, by linarith⟩
  have hmid : (T - s) / 2 ∈ Ioo (H.reference.tMinus - s) (T - s) :=
    ⟨by linarith, by linarith⟩
  let G := H.reference.flow.translate s hdom ordConnected_Ioo
    ⟨0, hzero, (T - s) / 2, hmid, by linarith⟩
  have htime : Ico (0 : ℝ) (T - s) ⊆ Ioo (H.reference.tMinus - s) (T - s) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hshift {t : ℝ} (ht : t ∈ Ico 0 (T - s)) : t + s ∈ Ico s T :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hbounds := SingularRegularLimit.uniform_spatial_metric_jet_bounds G isOpen_Ioo
    (sub_pos.mpr hsT) htime (isOpen_extChartAt_target q)
    (contMDiffOn_extChartAt_symm q)
    (fun _ hz => Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hz)
    (isCompact_closedBall (c q) r) htarget ha hb
    (fun t ht z hz v => hell (t + s) (hshift ht) z hz v)
    (fun k => by
      obtain ⟨K, _, hK⟩ := hcurv k
      exact ⟨K, fun t ht z hz => hK (t + s) (hshift ht) z hz⟩)
  refine ⟨s, r, hs, hsT, hr, htarget, hreg, ?_⟩
  intro m
  obtain ⟨B, hB, hbound⟩ := hbounds m
  refine ⟨B, hB, ?_⟩
  intro t ht z hz
  have h := hbound (t - s) ⟨by linarith [ht.1], by linarith [ht.2]⟩ z hz
  change ‖iteratedFDeriv ℝ m
    ((H.reference.flow.metric (t - s + s)).pullbackCoefficients c.symm) z‖ ≤ B at h
  simpa only [sub_add_cancel] using h

end PoincareConjecture.SingularTimeAssumptions
