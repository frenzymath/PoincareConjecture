import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Minimality
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Construction.CompactField
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.FirstVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Pullback.Congruence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.InteriorRegularity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable local instance : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace


theorem regularizedLGeodesicEquation_of_chart_momentum {J I : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ)
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2))
    (hI : IsOpen I) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I))
    {s : ℝ} (hs : s ∈ I) (x : M)
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J)
    (hmomentum : HasDerivAt
      (fun r ↦ chartMomentumVector
        (chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) r))
      (chartForceVector
        (spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (α s)))
        (spatialFDeriv (chartActionPotential F T x) (s, extChartAt (𝓡 n) x (α s)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) s)) s) :
    regularizedLGeodesicEquation F T α I E s := by
  have hαs := ((hα s hs).contMDiffAt (hI.mem_nhds hs)).mdifferentiableAt (by simp)
  have hnear : ∀ᶠ r in 𝓝 s,
      α r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source :=
    hαs.continuousAt ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hx)
  intro W
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let w := e.continuousLinearMapAt ℝ (α s) W
  have hw : chartFrame x w (α s) = W := e.symmL_continuousLinearMapAt hx W
  rw [← hw]
  have hscalar := (hasDerivAt_const s w).inner ℝ hmomentum
  simp only [chartMomentumVector_inner, chartForceVector_inner, inner_zero_left, add_zero]
    at hscalar
  have hmetric := parametricExtension_metric_pair_graph F T hI E hs hx hαs ht w
  have hmetric' := hmetric.congr_of_eventuallyEq (show
      (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) r) w) =ᶠ[𝓝 s] _ from by
    filter_upwards [hI.mem_nhds hs, hnear] with r hr hrx
    rw [chartActionMetric_apply F T hrx,
      chartFrame_curveVelocity hrx
        (((hα r hr).contMDiffAt (hI.mem_nhds hr)).mdifferentiableAt (by simp)),
      E.agrees r hr]
    simp only [curveVelocityWithin, curveVelocity,
      mfderivWithin_of_mem_nhds (hI.mem_nhds hr)])
  have hvalue := hscalar.unique hmetric'
  have hpot := chartActionPotential_spatial_apply F T hpotential hx ht w
  unfold regularizedEulerResidual scalarCurvatureDifferential
  rw [← hpot]
  linarith only [hvalue]

private theorem alongCurve_parameter_smul_contMDiffOn (α : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s)) {U : Set ℝ} (hU : IsOpen U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, Y s⟩ : TangentBundle (𝓡 n) M)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, s • Y s⟩ : TangentBundle (𝓡 n) M)) U := by
  intro s hs
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (α s)
  have hαs := (hα s hs).contMDiffAt (hU.mem_nhds hs)
  have hYs := (hY s hs).contMDiffAt (hU.mem_nhds hs)
  apply ContMDiffAt.contMDiffWithinAt
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hαs, ?_⟩
  have hcoord := (Bundle.contMDiffAt_totalSpace.mp hYs).2
  have hid : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun r : ℝ ↦ r) s := contMDiffAt_id
  apply (hid.smul hcoord).congr_of_eventuallyEq
  have hnear : ∀ᶠ r in 𝓝 s, α r ∈ e.baseSet :=
    hαs.continuousAt (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _))
  filter_upwards [hnear] with r hr
  change (e ⟨α r, r • Y r⟩).2 = r • (e ⟨α r, Y r⟩).2
  simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hr, map_smul]

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational
open ReducedLengthMinimum.Variation ReducedLengthMinimum.Variation.Geometry

variable {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ConnectedSpace M]

set_option maxHeartbeats 1200000 in

theorem minimizing_uniform_limit_regularizedLGeodesicEquation
    (K : AncientKappaSolution 2 M) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (paths : ℕ → BackwardTimePath K.flow 0 0 τ)
    (hanti : Antitone (fun k => backwardLLength K.flow 0 0 τ (paths k).curve))
    (hmin : Tendsto (fun k => backwardLLength K.flow 0 0 τ (paths k).curve)
      atTop (𝓝 (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ)))
    (γ : ℝ → M) (hγ : Continuous γ) (hγ0 : γ 0 = p)
    (hlim : TendstoUniformlyOn (fun k s => (paths k).curve (s ^ 2)) γ atTop
      (Icc 0 (Real.sqrt τ)))
    (E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) γ
      (curveVelocityWithin (n := 2) γ (Icc 0 (Real.sqrt τ))))
    {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τ)) :
    regularizedLGeodesicEquation K.flow 0 γ (Icc 0 (Real.sqrt τ)) E s := by
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 2)
  obtain ⟨m, t, x, Q, j, ht, hta, htb, hQ, _, hjs, hsj, _⟩ :=
    exists_compact_partition_at
      (fun x : M => (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
      (fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source)
      (fun y => ⟨y, mem_chart_source _ y⟩) hs γ hγ
  obtain ⟨w, hw, hsum⟩ := K.finite_chart_limit_le_spatialInfimum p hτ paths
    hanti hmin γ hγ hlim t ht hta htb x Q hQ
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source :=
    fun r hr => (hQ i).2.2 (interior_subset ((hQ i).2.1 (mem_image_of_mem γ hr)))
  have hsum' : (∑ i, chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum (γ 0) τ := by
    simpa only [chartH1Action, hγ0] using hsum
  have hlocal : IsChartH1Minimizer K.flow 0 (x j) (t j.castSucc) (t j.succ) γ (w j) := by
    intro ξ hξ hξa hξb hξsrc v hv
    exact K.chart_piece_minimal hτ t ht hta htb γ hγ.continuousOn x hsrc w hw hsum'
      j ξ hξ hξa hξb hξsrc v hv
  have htime (r : ℝ) (_hr : r ∈ Icc (t j.castSucc) (t j.succ)) :
      r ∈ interior ((fun q : ℝ => 0 - q ^ 2) ⁻¹' Iic (0 : ℝ)) := by
    have hpre : ((fun q : ℝ => 0 - q ^ 2) ⁻¹' Iic (0 : ℝ)) = univ := by
      ext q
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      nlinarith [sq_nonneg q]
    rw [hpre, interior_univ]
    exact mem_univ r
  have hmomentum := (chart_minimum_smooth_momentum K.flow 0
    K.regularizedPotential_contMDiff (hjs.trans hsj) (x j) γ hγ.continuousOn
    (hsrc j) htime (w j) (hw j) hlocal).2 s ⟨hjs, hsj⟩
  have hreg := K.chart_minimum_contMDiffOn (hjs.trans hsj) (x j) γ hγ.continuousOn
    (hsrc j) (w j) (hw j) hlocal
  have hIC : Ioo (t j.castSucc) (t j.succ) ⊆ Icc 0 (Real.sqrt τ) := by
    intro r hr
    constructor
    · have h := ht (Fin.zero_le j.castSucc)
      rw [hta] at h
      exact h.trans hr.1.le
    · have h := ht (Fin.le_last j.succ)
      rw [htb] at h
      exact hr.2.le.trans h
  let EI := restrictInteriorVelocityExtension isOpen_Ioo hIC γ E
  have hflow : 0 - s ^ 2 ∈ interior (Iic (0 : ℝ)) := by
    rw [interior_Iic]
    exact sub_neg.mpr (sq_pos_of_pos hs.1)
  have hEuler := regularizedLGeodesicEquation_of_chart_momentum K.flow 0
    K.regularizedPotential_contMDiff isOpen_Ioo γ (hreg.mono Ioo_subset_Icc_self)
    EI ⟨hjs, hsj⟩ (x j) (hsrc j ⟨hjs.le, hsj.le⟩) hflow hmomentum
  intro W
  have h := hEuler W
  unfold regularizedEulerResidual pullbackCovariantDerivative EI
    restrictInteriorVelocityExtension at h
  rw [curveVelocityWithin_eq_of_open_subset isOpen_Ioo hIC γ ⟨hjs, hsj⟩] at h
  exact h

set_option maxHeartbeats 1600000 in

theorem minimizing_uniform_limit_terminal_velocity_eq_zero
    (K : AncientKappaSolution 2 M) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (paths : ℕ → BackwardTimePath K.flow 0 0 τ)
    (hanti : Antitone (fun k => backwardLLength K.flow 0 0 τ (paths k).curve))
    (hmin : Tendsto (fun k => backwardLLength K.flow 0 0 τ (paths k).curve)
      atTop (𝓝 (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ)))
    (γ : ℝ → M) (hγ : Continuous γ) (hγ0 : γ 0 = p)
    (hlim : TendstoUniformlyOn (fun k s => (paths k).curve (s ^ 2)) γ atTop
      (Icc 0 (Real.sqrt τ)))
    (q : BackwardTimePath K.flow 0 0 τ)
    (hqmin : ∀ r : BackwardTimePath K.flow 0 0 τ, r.curve 0 = q.curve 0 →
      backwardLLength K.flow 0 0 τ q.curve ≤ backwardLLength K.flow 0 0 τ r.curve)
    (α : ℝ → M) (U : Set ℝ) (hU : IsOpen U) (hIU : Icc 0 (Real.sqrt τ) ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ α U)
    (hαγ : EqOn α γ (Icc 0 (Real.sqrt τ)))
    (hagrees : ∀ s ∈ Icc 0 (Real.sqrt τ), α s = q.curve (s ^ 2)) :
    curveVelocityWithin (n := 2) α (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0 := by
  let C := Icc 0 (Real.sqrt τ)
  have hc : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc hc
  let Y : ∀ s, TangentSpace (𝓡 2) (α s) := fun s ↦ s • curveVelocity (n := 2) α s
  have hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡 2)) ∞
      (fun s ↦ (⟨α s, Y s⟩ : TangentBundle (𝓡 2) M)) U :=
    alongCurve_parameter_smul_contMDiffOn α (curveVelocity (n := 2) α) hU hα
      (contMDiffOn_mfderiv_const_apply hU α hα 1)
  obtain ⟨V, hbase, hfield⟩ := K.exists_initialFixedLVariation_of_smooth_field
    q α Y U hU hIU hα hY hagrees (by simp only [Y, zero_smul])
  obtain ⟨D, hd⟩ := K.exists_regularized_firstVariation V.toLVariation
  have haction : variationSquareAction V.toLVariation =
      (fun u => regularizedLAction K.flow 0 τ (fun s => V.squareFamily s u)) :=
    funext (variationSquareAction_eq_regularizedLAction V.toLVariation)
  rw [← haction] at hd
  have hstationary := hasDerivAt_variationSquareAction_eq_zero hqmin V hd
  have hVγ : EqOn V.toLVariation.baseSquareCurve γ C := by
    rw [hbase]
    exact hαγ
  have hCeq : sqrtParameterInterval 0 τ = C := by
    simp only [sqrtParameterInterval, Real.sqrt_zero, C]
  have hres : firstVariationResidualIntegral V.toLVariation D = 0 := by
    unfold firstVariationResidualIntegral
    rw [Real.sqrt_zero]
    calc
      _ = ∫ s in (0 : ℝ)..Real.sqrt τ, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc.le
        intro s hs
        have hsC : s ∈ C := Ioo_subset_Icc_self hs
        let E : ParametricAlongCurveExtensionOn C V.toLVariation.baseSquareCurve
            (curveVelocityWithin (n := 2) V.toLVariation.baseSquareCurve C) := {
          extension := D.velocity_extension.extension
          domain := D.velocity_extension.domain
          open_domain := D.velocity_extension.open_domain
          graph_mem := fun r hr ↦ D.velocity_extension.graph_mem r (by
            simpa only [hCeq] using hr)
          smooth := D.velocity_extension.smooth
          agrees := fun r hr ↦ by
            have h := D.velocity_extension.agrees r (by simpa only [hCeq] using hr)
            simpa only [hCeq] using h }
        let Eγ := transferParametricExtension hVγ
          (fun r hr ↦ curveVelocityWithin_congr hVγ hr) E
        have heuler := K.minimizing_uniform_limit_regularizedLGeodesicEquation
          p hτ paths hanti hmin γ hγ hγ0 hlim Eγ hs
          (squareVariationField V.toLVariation s)
        have hVs : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 2) V.toLVariation.baseSquareCurve s := by
          rw [hbase]
          exact ((hα s (hIU hsC)).contMDiffAt (hU.mem_nhds (hIU hsC))).mdifferentiableAt
            (by simp)
        have hcongr := regularizedEulerResidual_congr K.flow 0 hVγ.symm Eγ E hsC
          (hC s hsC) hVs (squareVariationField V.toLVariation s)
        rw [hcongr] at heuler
        have heuler' : regularizedEulerResidual K.flow 0 V.toLVariation.baseSquareCurve
            (sqrtParameterInterval 0 τ) D.velocity_extension s
              (squareVariationField V.toLVariation s) = 0 := by
          simpa only [regularizedEulerResidual, pullbackCovariantDerivative, E, hCeq]
            using heuler
        dsimp only
        rw [heuler', neg_zero]
      _ = 0 := by simp only [intervalIntegral.integral_zero]
  rw [hres, add_zero] at hstationary
  have hvelocity (s : ℝ) (hs : s ∈ C) :
      curveVelocityWithin (n := 2) α C s = curveVelocity (n := 2) α s := by
    unfold curveVelocityWithin curveVelocity
    rw [mfderivWithin_eq_mfderiv ((hC s hs).uniqueMDiffWithinAt)
      (((hα s (hIU hs)).contMDiffAt (hU.mem_nhds (hIU hs))).mdifferentiableAt (by simp))]
  have hb : firstVariationBoundaryTerm V.toLVariation =
      Real.sqrt τ * (K.flow.metric (0 - (Real.sqrt τ) ^ 2)).inner (α (Real.sqrt τ))
        (curveVelocity (n := 2) α (Real.sqrt τ))
        (curveVelocity (n := 2) α (Real.sqrt τ)) := by
    unfold firstVariationBoundaryTerm
    dsimp only
    rw [Real.sqrt_zero, hfield (Real.sqrt τ) ⟨hc.le, le_rfl⟩,
      hfield 0 ⟨le_rfl, hc.le⟩, hbase, hCeq]
    simp only [Y, zero_smul, map_zero, sub_zero, map_smul, smul_eq_mul,
      hvelocity (Real.sqrt τ) ⟨hc.le, le_rfl⟩]
  rw [hb] at hstationary
  have hnorm := (mul_eq_zero.mp hstationary).resolve_left hc.ne'
  rw [hvelocity (Real.sqrt τ) ⟨hc.le, le_rfl⟩]
  by_contra hv
  exact (ne_of_gt ((K.flow.metric (0 - (Real.sqrt τ) ^ 2)).pos (α (Real.sqrt τ))
    (curveVelocity (n := 2) α (Real.sqrt τ)) hv)) hnorm

end PoincareConjecture.AncientKappaSolution
