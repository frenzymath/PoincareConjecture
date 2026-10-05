import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Coordinates.TerminalClosedCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Flow.FlowLocality
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.RicciOperatorEvaluation
import PoincareLib.Geometry.RicciFlow.MetricFamily.Coordinates

/-!
# The actual Ricci flow including its terminal slice

The closed family keeps the old metric and connection records at every
earlier time, and uses the complete terminal metric at the endpoint.
The coefficient regularity and equation give a genuine Ricci flow on
the whole closed slab. This is the bounded-curvature terminal extension
in Morgan-Tian Theorem 12.5, pp. 296-297, not yet a forward restart.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Actual coefficient derivatives have nested continuous-linear-map targets.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34.PartialFlowTerminalJets

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S) (P : RicciFlowCurvatureTheory.{0})
  (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)

/-- The closed metric/connection pair keeps the exact old dependent
records before the terminal slice (Theorem 12.5, pp. 296-297). -/
noncomputable def closedMetricConnection (t : ℝ) :
    Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g :=
  if t < S then ⟨F.flow.metric t, F.flow.connection t⟩ else
    let g := L.metric P E0 hS hSF hB hfull
    ⟨g, g.euclideanLeviCivitaData⟩

/-- The actual terminally closed metric family (Theorem 12.5, pp. 296-297). -/
noncomputable def closedMetric (t : ℝ) : RiemannianMetric 3 StandardCapSpace :=
  (L.closedMetricConnection P E0 hS hSF hB hfull t).1

/-- Its retained compatible connection family (Theorem 12.5, pp. 296-297). -/
noncomputable def closedConnection (t : ℝ) :
    LeviCivitaData (L.closedMetric P E0 hS hSF hB hfull t) :=
  (L.closedMetricConnection P E0 hS hSF hB hfull t).2

/-- Before the terminal time the whole metric/connection sigma pair is
literally the old pair (Theorem 12.5, pp. 296-297). -/
theorem closedMetricConnection_of_lt {t : ℝ} (ht : t < S) :
    L.closedMetricConnection P E0 hS hSF hB hfull t =
      ⟨F.flow.metric t, F.flow.connection t⟩ := by
  simp only [closedMetricConnection, ht, if_true]

/-- Earlier metric records are retained exactly (Theorem 12.5, pp. 296-297). -/
theorem closedMetric_of_lt {t : ℝ} (ht : t < S) :
    L.closedMetric P E0 hS hSF hB hfull t = F.flow.metric t := by
  simp only [closedMetric, L.closedMetricConnection_of_lt P E0 hS hSF hB hfull ht]

/-- At the endpoint the family uses the actual constructed terminal
metric (Theorem 12.5, pp. 296-297). -/
theorem closedMetric_terminal :
    L.closedMetric P E0 hS hSF hB hfull S = L.metric P E0 hS hSF hB hfull := by
  simp only [closedMetric, closedMetricConnection, lt_self_iff_false, if_false]

/-- Every total time slice has exactly the closed coefficient field
(Theorem 12.5, pp. 296-297). -/
theorem closedMetric_coefficients (t : ℝ) :
    (L.closedMetric P E0 hS hSF hB hfull t).euclideanCoefficients =
      fun x => L.closedCoefficients (t, x) := by
  by_cases ht : t < S
  · rw [L.closedMetric_of_lt P E0 hS hSF hB hfull ht]
    funext x
    exact (L.closedCoefficients_of_lt ht x).symm
  · simp only [closedMetric, closedMetricConnection, ht, if_false]
    rw [L.metric_coefficients]
    funext x
    exact (L.closedCoefficients_of_le (not_lt.mp ht) x).symm

/-- The actual metric section is jointly smooth on the entire closed
time slab (Theorem 12.5, pp. 296-297). -/
theorem closedMetric_smooth :
    RiemannianMetric.IsSmoothFamilyOn (L.closedMetric P E0 hS hSF hB hfull) (Icc 0 S) := by
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart (fun _ _ => rfl)
    (L.closedMetric P E0 hS hSF hB hfull) L.closedCoefficients
  · have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × StandardCapSpace) ∞
        (fun p : ℝ × StandardCapSpace => (p.1, p.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact (L.contDiffOn_closedCoefficients P E0 hS hSF hB hfull).contMDiffOn.comp
      hmap.contMDiffOn (fun _ hp => hp)
  · intro t _ht x u v
    exact congrArg (fun A => A x u v) (L.closedMetric_coefficients P E0 hS hSF hB hfull t)

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient operator is evaluated on the actual retained connection.
/-- The geometric Ricci equation holds on the positive slab including
its terminal endpoint (Theorem 12.5, pp. 296-297). -/
theorem closedMetric_equation_Ioc {t : ℝ} (ht : t ∈ Ioc 0 S) (x u v : StandardCapSpace) :
    HasDerivWithinAt (fun s => (L.closedMetric P E0 hS hSF hB hfull s).inner x u v)
      (-2 * (L.closedConnection P E0 hS hSF hB hfull t).ricci x u v) (Ioc 0 S) t := by
  have h := ((L.hasDerivWithinAt_closedCoefficients_Ioc P E0 hS hSF hB hfull ht x).clm_apply
    (hasDerivWithinAt_const t (Ioc 0 S) u)).clm_apply
      (hasDerivWithinAt_const t (Ioc 0 S) v)
  have hop : jetRicciFlowOperator 3 (spatialJet 2 L.closedCoefficients (t, x)) u v =
      -2 * (L.closedConnection P E0 hS hSF hB hfull t).ricci x u v := by
    rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet,
      ← L.closedMetric_coefficients P E0 hS hSF hB hfull t]
    exact ricciFlowOperator_metricTwoJet_apply
      (L.closedConnection P E0 hS hSF hB hfull t) x u v
  have hfunction : (fun s => (L.closedMetric P E0 hS hSF hB hfull s).inner x u v) =
      (fun s => L.closedCoefficients (s, x) u v) :=
    funext (fun s => congrArg (fun A => A x u v)
      (L.closedMetric_coefficients P E0 hS hSF hB hfull s))
  rw [hfunction]
  simpa only [map_zero, add_zero, zero_add, hop] using h

/-- Locality retains the original initial equation and the new terminal
equation on one closed slab (Theorem 12.5, pp. 296-297). -/
theorem closedMetric_equation {t : ℝ} (ht : t ∈ Icc 0 S) (x u v : StandardCapSpace) :
    HasDerivWithinAt (fun s => (L.closedMetric P E0 hS hSF hB hfull s).inner x u v)
      (-2 * (L.closedConnection P E0 hS hSF hB hfull t).ricci x u v) (Icc 0 S) t := by
  by_cases hlt : t < S
  · have hnear : Iio S ∈ 𝓝[Icc 0 S] t := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)
    have hdom : Ico 0 F.lifetime ∈ 𝓝[Icc 0 S] t := by
      filter_upwards [self_mem_nhdsWithin, hnear] with s hs hsS
      exact ⟨hs.1, hsS.trans_le hSF⟩
    rw [ricci_eq_of_metric_eq (L.closedMetric_of_lt P E0 hS hSF hB hfull hlt)
      (L.closedConnection P E0 hS hSF hB hfull t) (F.flow.connection t)]
    have hd := (F.flow.equation t ⟨ht.1, hlt.trans_le hSF⟩ x u v).mono_of_mem_nhdsWithin hdom
    apply hd.congr_of_eventuallyEq_of_mem _ ht
    filter_upwards [hnear] with s hs
    rw [L.closedMetric_of_lt P E0 hS hSF hB hfull hs]
  · have hpos : 0 < t := hS.trans_le (not_lt.mp hlt)
    have hnear : Ioi 0 ∈ 𝓝[Icc 0 S] t := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hpos)
    have hdom : Ioc 0 S ∈ 𝓝[Icc 0 S] t := by
      filter_upwards [self_mem_nhdsWithin, hnear] with s hs hspos
      exact ⟨hspos, hs.2⟩
    have hd := L.closedMetric_equation_Ioc P E0 hS hSF hB hfull ⟨hpos, ht.2⟩ x u v
    exact hd.mono_of_mem_nhdsWithin hdom

/-- A bounded-curvature partial flow extends to an actual Ricci flow on
the closed terminal slab (Theorem 12.5, pp. 296-297). -/
noncomputable def closedFlow : RicciFlow 3 StandardCapSpace (Icc 0 S) where
  metric := L.closedMetric P E0 hS hSF hB hfull
  connection := L.closedConnection P E0 hS hSF hB hfull
  interval := ordConnected_Icc
  nontrivial := ⟨0, ⟨le_rfl, hS.le⟩, S, ⟨hS.le, le_rfl⟩, hS.ne⟩
  smooth := L.closedMetric_smooth P E0 hS hSF hB hfull
  equation t ht x u v := L.closedMetric_equation P E0 hS hSF hB hfull (t := t) ht x u v

/-- Every included slice of the terminally closed flow is complete for
its actual Riemannian path distance (Theorem 12.5, pp. 296-297). -/
theorem closedFlow_complete {t : ℝ} (ht : t ∈ Icc 0 S) :
    MetricComplete ((L.closedFlow P E0 hS hSF hB hfull).metric t) := by
  change MetricComplete (L.closedMetric P E0 hS hSF hB hfull t)
  rcases ht.2.eq_or_lt with heq | hlt
  · subst t
    rw [L.closedMetric_terminal]
    exact L.metric_complete P E0 hS hSF hB hfull
  · rw [L.closedMetric_of_lt P E0 hS hSF hB hfull hlt]
    exact partialFlow_complete F P ⟨ht.1, hlt.trans_le hSF⟩

end PoincareMT.M34.PartialFlowTerminalJets
