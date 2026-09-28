import PoincareConjecture.Proofs.M14.Sec6_3_InitialValuePasting
import PoincareConjecture.Proofs.M14.Sec6_3_EulerGaugePhase
import PoincareConjecture.Proofs.M14.Sec6_3_PhasePath
import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerExistence

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem exists_initialValuePath_realizing_phase_continuation
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) {T l r d : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hrd : r < d)
    {x y : G.Point} {Z : G.Horizontal x}
    (P : M14SquareRootInitialValuePath G T (r ^ 2) x y Z)
    (β₀ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    (hβ₀ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β₀ (Icc l r))
    (hrec₀ : ∀ s ∈ Icc l r, (G.gaugeCover.cylinder b).toSpacetime (β₀ s) = P.square_path.curve s)
    (htime : ∀ s ∈ Icc l d, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    (ψ : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (hψ : ContDiffOn ℝ ∞ ψ (Icc l d))
    (hmap : ∀ s ∈ Icc l d, (ψ s).1 ∈ (extChartAt (𝓡 n) x₀).target)
    (hphase : ∀ s ∈ Icc l d, HasDerivWithinAt ψ
      (M08.closedChartEulerPhase W.flow T x₀ (Icc l d) s (ψ s)) (Icc l d) s)
    (hi : ψ r = ((β₀ r).2.val,
      M08.chartMomentumVector (M08.chartActionMetric W.flow T x₀ (r, (β₀ r).2.val))
        (derivWithin (fun s => (β₀ s).2.val) (Icc l r) r)))
    (β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    (hβclock : ∀ s ∈ Icc l d, (β s).1.val = T - s ^ 2)
    (hβcoord : ∀ s ∈ Icc l d, (β s).2.val = (ψ s).1) :
    ∃ z : G.Point, ∃ Q : M14SquareRootInitialValuePath G T (d ^ 2) x z Z,
      EqOn Q.square_path.curve (fun s => (G.gaugeCover.cylinder b).toSpacetime (β s))
        (Icc l d) := by
  have hr : 0 < r := hl.trans_lt hlr
  have hd : 0 < d := hr.trans hrd
  have hC : M14SqrtParameterInterval (l ^ 2) (d ^ 2) = Icc l d := by
    rw [M14SqrtParameterInterval, Real.sqrt_sq hl, Real.sqrt_sq hd.le]
  have hsub : Icc l r ⊆ Icc l d := Icc_subset_Icc le_rfl hrd.le
  have hsubP : Icc l r ⊆ M14SqrtParameterInterval 0 (r ^ 2) := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hr.le]
    exact Icc_subset_Icc hl le_rfl
  have hclock₀ (s : ℝ) (hs : s ∈ Icc l r) : (β₀ s).1.val = T - s ^ 2 :=
    ((G.gaugeCover.cylinder b).time_eq (β₀ s)).symm.trans
      ((congrArg G.spacetime.timeFunction (hrec₀ s hs)).trans
        (P.square_path.curve_time s (hsubP hs)))
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  have hphase₀ := squareRootEuler_gauge_phase P.square_path b hCoordinates hscalar W hM04 x₀
    hlr hsubP hβ₀ hrec₀ hclock₀ P.extension (fun s hs => P.euler s (hsubP hs))
  have hsrc (s : ℝ) (_hs : s ∈ Icc l r) : (β₀ s).2.val ∈ (extChartAt (𝓡 n) x₀).target := by
    have hval : extChartAt (𝓡 n) x₀ (β₀ s).2 = (β₀ s).2.val := by
      rw [extChartAt_coe]
      rfl
    rw [← hval]
    apply (extChartAt (𝓡 n) x₀).map_source
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  have hsmall (s : ℝ) (hs : s ∈ Icc l r) : HasDerivWithinAt ψ
      (M08.closedChartEulerPhase W.flow T x₀ (Icc l r) s (ψ s)) (Icc l r) s := by
    rw [closedChartEulerPhase_restrict W.flow hM04 T x₀ htime hsub hs (hmap s (hsub hs))]
    exact (hphase s (hsub hs)).mono hsub
  have hsame := closedChartEulerPhase_unique W.flow hM04 T x₀ hlr
    (fun s hs => htime s (hsub hs)) hsrc hphase₀ hsmall ⟨hlr.le, le_rfl⟩ hi.symm
  obtain ⟨θ, _, hθclock, hθcoord, p, R, E, _, hR, hEuler, _⟩ :=
    exists_gaugeEulerPath_of_phase hM04 hM12 b W t₀ x₀ (sq_nonneg l)
      ((sq_lt_sq₀ hl hd.le).mpr (hlr.trans hrd))
      (by simpa only [hC] using htime) (q := fun s => (ψ s).1) (P := fun s => (ψ s).2)
      (by simpa only [hC] using hψ.fst) (by rw [hC]; exact hmap)
      (by simpa only [hC, Prod.eta] using hphase)
  have hoverlap : EqOn P.square_path.curve R.curve (M14SqrtParameterInterval (l ^ 2) (r ^ 2)) := by
    intro s hs₀
    have hs : s ∈ Icc l r := by
      simpa only [M14SqrtParameterInterval, Real.sqrt_sq hl, Real.sqrt_sq hr.le] using hs₀
    have hsC : s ∈ M14SqrtParameterInterval (l ^ 2) (d ^ 2) := hC ▸ hsub hs
    have hθ : β₀ s = θ s := Prod.ext
      (Subtype.ext ((hclock₀ s hs).trans (hθclock s hsC).symm))
      (Subtype.ext ((congrArg Prod.fst (hsame hs)).trans (hθcoord s hsC).symm))
    exact (hrec₀ s hs).symm.trans
      ((congrArg (G.gaugeCover.cylinder b).toSpacetime hθ).trans (hR s hsC).symm)
  obtain ⟨z, Q, _, htail⟩ := exists_initialValuePath_of_overlap hM12 P R E hEuler
    ((sq_lt_sq₀ hl hr.le).mpr hlr) ((sq_lt_sq₀ hr.le hd.le).mpr hrd) hoverlap
  refine ⟨z, Q, ?_⟩
  intro s hs
  have hsC : s ∈ M14SqrtParameterInterval (l ^ 2) (d ^ 2) := hC ▸ hs
  have hθ : θ s = β s := Prod.ext
    (Subtype.ext ((hθclock s hsC).trans (hβclock s hs).symm))
    (Subtype.ext ((hθcoord s hsC).trans (hβcoord s hs).symm))
  exact (htail hsC).trans
    ((hR s hsC).trans (congrArg (G.gaugeCover.cylinder b).toSpacetime hθ))

end PoincareConjecture.M14
