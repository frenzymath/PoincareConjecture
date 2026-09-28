import PoincareConjecture.Proofs.M35.CapGeometry.SelectedIntrinsicShapeJets
import PoincareConjecture.Proofs.M35.CapGeometry.SphereLineChartTime
import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable (P : M35StandardCapPredecessors)
  {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
  (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
  (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
  (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
  (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
    (blowupBackwardInterval ⊤))

noncomputable def selectedIntrinsicShapeDerivative (k m : ℕ)
    (z : L.limit.sliceCarrier.carrier) : ℝ :=
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G : RiemannianMetric 3 V := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
  let hrot := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t (L.subsequence k)) (ht _)) Q hQ
  let hc := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence k)))
    (E.complete (t (L.subsequence k)) (ht _)) Q hQ
  let y := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  iteratedDeriv m (intrinsicRadialShape G hrot hc) (radialArclength G ‖y‖)

theorem blowupSequence_intrinsic_shape_moving_tendsto_zero
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    {kappa : ℝ} (A : BlowupAncientKappaIdentification L.limit kappa) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ (_N : M27SphereLineFlowCertificate A.solution)
      (idx : ℕ → ℕ), Tendsto idx atTop atTop →
      ∀ (z : ℕ → L.limit.sliceCarrier.carrier) (z₀ : L.limit.sliceCarrier.carrier),
        Tendsto z atTop (𝓝 z₀) → ∀ m : ℕ,
          Tendsto (fun k => selectedIntrinsicShapeDerivative P E t x ht hR L
            (idx k) m (z k)) atTop (𝓝 0) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  classical
  intro N idx hidx z z₀ hz m
  let q := (N.identification.symm z₀).1
  let c := chartAt E2 q
  let coordinate := N.identification ∘ cylinderChart q
  let psi (y : L.limit.sliceCarrier.carrier) : V :=
    cylinderCoordinateEquiv.symm
      (c (N.identification.symm y).1, (N.identification.symm y).2)
  have hsource : ∀ᶠ k in atTop, (N.identification.symm (z k)).1 ∈ c.source := by
    have h := ((continuous_fst.comp N.identification.symm.contMDiff.continuous).tendsto z₀).comp hz
    exact h.eventually (c.open_source.mem_nhds (mem_chart_source E2 q))
  have hpsi : ContinuousAt psi z₀ := by
    have hi : ContinuousAt N.identification.symm z₀ :=
      N.identification.symm.contMDiff.continuous.continuousAt
    exact cylinderCoordinateEquiv.symm.continuous.continuousAt.comp
      ((c.continuousAt (mem_chart_source E2 q)).comp hi.fst |>.prodMk hi.snd)
  let p₀ := psi z₀
  let K : Set V := Metric.closedBall p₀ 1
  let Ω : Set V := Metric.ball p₀ 2
  have hK : IsCompact K := isCompact_closedBall p₀ 1
  have hKΩ : K ⊆ Ω := Metric.closedBall_subset_ball (by norm_num)
  have hcompact : IsCompact (closure Ω) :=
    (isCompact_closedBall p₀ 2).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hp : ∀ᶠ k in atTop, psi (z k) ∈ K :=
    (hpsi.tendsto.comp hz).eventually (Metric.closedBall_mem_nhds p₀ (by norm_num))
  let p (k : ℕ) : V := if psi (z k) ∈ K then psi (z k) else p₀
  have hpK (k : ℕ) : p k ∈ K := by
    dsimp only [p]
    split_ifs with hk
    · exact hk
    · exact Metric.mem_closedBall_self (by norm_num)
  let g := sphereLineChartMetric N 0 q
  have hg : g.euclideanCoefficients = (L.limit.flow.metric 0).pullbackCoefficients
      coordinate := by
    change (A.solution.flow.metric 0).pullbackCoefficients coordinate = _
    rw [A.metric_eq 0 le_rfl]
  have hjet := blowupSequence_intrinsic_shape_jets_zero P E t x ht hR hd L
    coordinate (sphereLineChart_contMDiff N q) (sphereLineChart_invertible N q)
    g hg Ω Metric.isOpen_ball hcompact m 0 K hK hKΩ idx hidx p hpK
  have hval := ((continuousMultilinearCurryFin0 ℝ V ℝ).continuous.tendsto 0).comp hjet
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
    LinearIsometryEquiv.apply_symm_apply, map_zero] at hval
  apply hval.congr'
  filter_upwards [hp, hsource] with k hpk hsk
  have hmap : coordinate (p k) = z k := by
    simp only [p, if_pos hpk, coordinate, Function.comp_apply, psi, cylinderChart,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [c.left_inv hsk]
    exact N.identification.apply_symm_apply (z k)
  change selectedIntrinsicShapeDerivative P E t x ht hR L (idx k) m
    (coordinate (p k)) = _
  rw [hmap]

theorem blowupSequence_intrinsic_shape_uniform_compact
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    {kappa : ℝ} (A : BlowupAncientKappaIdentification L.limit kappa) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ (_N : M27SphereLineFlowCertificate A.solution)
      (K : Set L.limit.sliceCarrier.carrier), IsCompact K → ∀ m : ℕ,
      ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop, ∀ z ∈ K,
        |selectedIntrinsicShapeDerivative P E t x ht hR L k m z| < epsilon := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  let : MetricSpace L.limit.carrier.carrier := Proofs.M09.selectedMetricSpace
    (L.limit.flow.metric 0)
  intro N K hK m epsilon hepsilon
  obtain ⟨n, hn⟩ := uniform_of_moving_point_limits
    (F := fun k z => selectedIntrinsicShapeDerivative P E t x ht hR L k m z)
    (G := fun _ => 0) hK continuousOn_const
    (fun idx hidx z _ z₀ _ hz => blowupSequence_intrinsic_shape_moving_tendsto_zero
      P E t x ht hR L hd A N idx hidx z z₀ hz m) hepsilon
  filter_upwards [eventually_ge_atTop n] with k hk z hz
  simpa only [sub_zero] using hn k hk z hz

end PoincareConjecture.M35.OrdinaryRealization
