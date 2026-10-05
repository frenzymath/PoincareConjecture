import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.RetainedClosedCoefficients
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.CoordinateFlowRealization
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.RetainedChartFlows
import PoincareLib.Geometry.RicciFlow.Harnack.Regularity

/-!
# Actual finite flows on retained local charts

The closed coefficient limit and actual retained chart pullbacks supply
the coordinate flow-realization theorem. The resulting flow includes both
time endpoints, while its coefficient field retains the original sequence's
mixed within jets on the closed spatial buffer.

Reference: Morgan--Tian Definition 5.12 and Proposition 5.14, pp. 90-91.
The lower flow supplier and the mixed coefficient bounds remain explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

set_option synthInstance.maxHeartbeats 100000 in
-- The full bilinear within-jet spaces need additional dependent instance search.
set_option maxHeartbeats 800000 in
-- The retained dependent metric fields and domain identities require extra reduction.
/-- Positive retained coefficient limits construct an actual local flow on
the closed time interval, preserving the original closed-cylinder jets
(Definition 5.12 and Proposition 5.14, pp. 90-91). -/
theorem exists_closed_flow_on_retained_chart
    (hFlow : WithinBilinearFlowService.{0})
    {n : ℕ} {T τ : ℝ} (hτ : 0 < τ) (hτT : τ < T)
    {S : PointedFlowSequence n (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (Fsrc : ∀ k, RicciFlow n (S.carrier k).carrier (Icc (-T) 0))
    (hmetric : ∀ k t, (Fsrc k).metric t =
      (S.flow k).flow.metric (t + T / 2))
    (q : G.limitCarrier.carrier) (x₀ : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ (extChartAt (𝓡 n) q).target)
    (α : ℝ) (hα : 0 < α) :
    let U : Opens (EuclideanSpace ℝ (Fin n)) :=
      ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩
    let Ω := Icc (-τ) 0 ×ˢ Metric.closedBall x₀ r
    let f := fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
      ((Fsrc (G.subsequence k)).metric z.1).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
          (extChartAt (𝓡 n) q).symm) z.2
    let g := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (G.limitFlow.flow.metric (z.1 + T / 2)).pullbackCoefficients
        (extChartAt (𝓡 n) q).symm z.2
    (∀ᶠ k : ℕ in atTop, ∀ z ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n),
      α * ‖v‖ ^ 2 ≤ f k z v v) →
    (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop, ∀ z ∈ Ω,
      ‖iteratedFDerivWithin ℝ m (f k) Ω z‖ ≤ C) →
    ∃ B : (ℝ × EuclideanSpace ℝ (Fin n)) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      ∃ Fchart : RicciFlow n U (Icc (-τ) 0),
        ContDiffOn ℝ ∞ B Ω ∧ EqOn B g (interior Ω) ∧
        (∀ z ∈ Ω, ∀ v w : EuclideanSpace ℝ (Fin n),
          B z v w = B z w v) ∧
        (∀ z ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n),
          α * ‖v‖ ^ 2 ≤ B z v v) ∧
        (∀ t ∈ Icc (-τ) 0, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
          (Fchart.metric t).inner x v w = B (t, x) v w) ∧
        ∀ m : ℕ, TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m (f k) Ω)
          (iteratedFDerivWithin ℝ m B Ω) atTop Ω := by
  classical
  intro U Ω f g hellip hbounds
  obtain ⟨B, hB, hBg, hsymm, hlower, hjets⟩ :=
    exists_closed_coefficient_limit_on_retained_chart
      hτ hτT G Fsrc hmetric q x₀ hr hball α hellip hbounds
  have htime : -τ < 0 := by linarith
  have hsub : Icc (-τ) 0 ⊆ Icc (-T) 0 := by
    rintro t ⟨ht, ht0⟩
    exact ⟨by linarith, ht0⟩
  have hnontrivial : (Icc (-τ) (0 : ℝ)).Nontrivial :=
    ⟨-τ, ⟨le_rfl, htime.le⟩, 0, ⟨htime.le, le_rfl⟩, htime.ne⟩
  let Fshort (j : ℕ) : RicciFlow n (S.carrier j).carrier (Icc (-τ) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow
      (Fsrc j) hsub ordConnected_Icc hnontrivial
  have hshort (j : ℕ) (t : ℝ) : (Fshort j).metric t = (Fsrc j).metric t := rfl
  have hzero : -T / 2 < 0 ∧ 0 < T / 2 := by constructor <;> linarith
  obtain ⟨N, H, hH⟩ := exists_source_flows_on_retained_chart
    G hzero Fshort q U (Metric.closedBall x₀ r) (isCompact_closedBall x₀ r)
    Metric.ball_subset_closedBall hball
  let Bseq (k : ℕ) := f (max N k)
  have hcoeff (k : ℕ) (t : ℝ) (x : U) (v w : TangentSpace (𝓡 n) x) :
      ((H k).metric t).inner x v w = Bseq k (t, x) v w := by
    simpa only [Bseq, f, hshort] using hH k t x v w
  have hrepair (m : ℕ) : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (Bseq k) Ω)
      (iteratedFDerivWithin ℝ m B Ω) atTop Ω := by
    apply (hjets m).congr
    filter_upwards [eventually_ge_atTop N] with k hk
    intro z _
    change iteratedFDerivWithin ℝ m (f k) Ω z = iteratedFDerivWithin ℝ m (Bseq k) Ω z
    simp only [Bseq, max_eq_right hk]
  let Γ : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
    Icc (-τ) 0 ×ˢ (U : Set (EuclideanSpace ℝ (Fin n)))
  let O : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
    (univ : Set ℝ) ×ˢ (U : Set (EuclideanSpace ℝ (Fin n)))
  have hΓΩ : Γ ⊆ Ω := fun z hz =>
    ⟨hz.1, Metric.ball_subset_closedBall hz.2⟩
  have hΓ : Γ = Ω ∩ O := by
    ext z
    constructor
    · intro hz
      exact ⟨hΓΩ hz, ⟨mem_univ _, hz.2⟩⟩
    · intro hz
      exact ⟨hz.1.1, hz.2.2⟩
  have hO : IsOpen O := isOpen_univ.prod U.isOpen
  have hjet (A : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (m : ℕ) (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ Γ) :
      iteratedFDerivWithin ℝ m A Γ z = iteratedFDerivWithin ℝ m A Ω z := by
    rw [hΓ]
    exact iteratedFDerivWithin_inter_open hO ⟨mem_univ _, hz.2⟩
  have hconv (m : ℕ) (K : Set (ℝ × EuclideanSpace ℝ (Fin n))) (hKΓ : K ⊆ Γ) :
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (Bseq k) Γ)
        (iteratedFDerivWithin ℝ m B Γ) atTop K := by
    exact (((hrepair m).mono (hKΓ.trans hΓΩ)).congr
      (Eventually.of_forall fun k z hz => (hjet (Bseq k) m z (hKΓ hz)).symm)).congr_right
      (fun z hz => (hjet B m z (hKΓ hz)).symm)
  obtain ⟨Fchart, hFchart⟩ := exists_flow_of_coordinate_coefficients hFlow U
    (uniqueDiffOn_Icc htime) H Bseq B (hB.mono hΓΩ)
    (fun k t _ x v w => hcoeff k t x v w)
    (fun t ht x hx v w => hsymm (t, x) (hΓΩ ⟨ht, hx⟩) v w)
    (fun t ht x hx => ⟨α, hα, fun v => hlower (t, x) (hΓΩ ⟨ht, hx⟩) v⟩)
    (fun m K _ hKΓ => hconv m K hKΓ)
  exact ⟨B, Fchart, hB, hBg, hsymm, hlower, hFchart, hjets⟩

end PoincareMT.M30
