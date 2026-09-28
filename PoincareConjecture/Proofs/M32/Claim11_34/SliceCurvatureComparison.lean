import PoincareConjecture.Proofs.M32.Claim11_34.SliceMetricJets
import PoincareConjecture.Proofs.M32.Claim11_34.CompactRicciJets
import PoincareConjecture.Proofs.M32.Claim11_34.ScalarPullbackJet
import PoincareConjecture.Proofs.M32.Mathlib.RelativeBilinearError
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.BilinearConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

open SpacetimeBounds

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

private noncomputable def comparisonMetric (G : GeneralizedBlowupConvergence S J)
    (t : ℝ) (k : ℕ) :=
  rescaledMetric ((S.flow (G.subsequence k)).metric
    ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
    (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))

private noncomputable def comparisonConnection (G : GeneralizedBlowupConvergence S J)
    (t : ℝ) (k : ℕ) : LeviCivitaData (comparisonMetric G t k) :=
  rescaledMetric_connection ((S.flow (G.subsequence k)).metric
    ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
    ((S.flow (G.subsequence k)).connection
      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
    (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))

private noncomputable def comparisonChart (G : GeneralizedBlowupConvergence S J)
    (q : G.limit.carrier.carrier) (t : ℝ) (k : ℕ)
    (htk : t ∈ Icc (-G.exhaustion.time k) 0) :=
  (G.embedding k).forward t htk ∘ (extChartAt (𝓡 3) q).symm

private theorem comparisonChart_domains
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    {t : ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (htime : ∀ i, t ∈ Icc (-G.exhaustion.time (sigma i)) 0) :
    ∀ᶠ i in atTop, ∃ V : Set (EuclideanSpace ℝ (Fin 3)),
      IsOpen V ∧ K ⊆ V ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (comparisonChart G q t (sigma i) (htime i)) V ∧
      ∀ y ∈ V, (mfderiv (𝓡 3) (𝓡 3)
        (comparisonChart G q t (sigma i) (htime i)) y).IsInvertible := by
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G
    (hK.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hKc))
  filter_upwards [hsigma.eventually (eventually_ge_atTop j)] with i hi
  let V := (extChartAt (𝓡 3) q).target ∩
    (extChartAt (𝓡 3) q).symm ⁻¹' G.exhaustion.space (sigma i)
  have hV : IsOpen V := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) (G.exhaustion.space_open (sigma i))
  refine ⟨V, hV, fun y hy => ⟨hKc hy,
    G.exhaustion.space_increasing hi (hj (mem_image_of_mem _ hy))⟩, ?_, ?_⟩
  · exact ((G.embedding (sigma i)).forward_smooth t (htime i)).comp
      ((contMDiffOn_extChartAt_symm (n := ∞) q).mono inter_subset_left)
      (fun _ hy => hy.2)
  · intro y hy
    have hf := ((G.embedding (sigma i)).forward_smooth t (htime i)).contMDiffAt
      ((G.exhaustion.space_open (sigma i)).mem_nhds hy.2)
    have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hy.1)
    have hbij := cylinder_forward_mfderiv_bijective (G.embedding (sigma i))
      (G.exhaustion.space_open (sigma i)) t (htime i) hy.2
    have hfi : (mfderiv (𝓡 3) (𝓡 3) ((G.embedding (sigma i)).forward t (htime i))
        ((extChartAt (𝓡 3) q).symm y)).IsInvertible := by
      let : T2Space (TangentSpace (𝓡 3) ((extChartAt (𝓡 3) q).symm y)) := by
        unfold TangentSpace
        infer_instance
      let : T2Space (TangentSpace (𝓡 3)
          ((G.embedding (sigma i)).forward t (htime i) ((extChartAt (𝓡 3) q).symm y))) := by
        unfold TangentSpace
        infer_instance
      let : FiniteDimensional ℝ
          (TangentSpace (𝓡 3) ((extChartAt (𝓡 3) q).symm y)) := by
        unfold TangentSpace
        infer_instance
      let A := mfderiv (𝓡 3) (𝓡 3) ((G.embedding (sigma i)).forward t (htime i))
        ((extChartAt (𝓡 3) q).symm y)
      let e := LinearEquiv.ofBijective A.toLinearMap hbij
      exact ⟨e.toContinuousLinearEquiv, rfl⟩
    rw [comparisonChart, mfderiv_comp y (hf.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp))]
    exact hfi.comp (Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hy.1)

private noncomputable def coordinateRicci
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (phi : EuclideanSpace ℝ (Fin 3) → M) (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := by
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (phi y)) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (phi y)) := by
    unfold TangentSpace
    infer_instance
  let : T2Space (TangentSpace (𝓡 3) (phi y)) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (phi y)) := by
    unfold TangentSpace
    infer_instance
  exact ContinuousLinearMap.bilinearComp
    (E := TangentSpace (𝓡 3) (phi y)) (F := TangentSpace (𝓡 3) (phi y)) (G := ℝ)
    (E' := EuclideanSpace ℝ (Fin 3)) (F' := EuclideanSpace ℝ (Fin 3))
    (M13.ricciLinear D (phi y)).toContinuousBilinearMap
    (mfderiv (𝓡 3) (𝓡 3) phi y) (mfderiv (𝓡 3) (𝓡 3) phi y)

private theorem comparison_chart_metric_positive
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier) (t : ℝ)
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ (extChartAt (𝓡 3) q).target)
    (v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) :
    0 < (G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm y v v := by
  apply (G.limit.flow.metric t).pos
  intro hz
  apply hv
  apply (Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hy).injective
  rw [map_zero]
  convert! hz using 1

private theorem comparison_chart_Ricci
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (q : G.limit.carrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (htime : ∀ i, t ∈ Icc (-G.exhaustion.time (sigma i)) 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ i in atTop, ∀ y ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3),
      |coordinateRicci (comparisonConnection G t (sigma i))
          (comparisonChart G q t (sigma i) (htime i)) y v v -
        coordinateRicci (G.limit.flow.connection t) (extChartAt (𝓡 3) q).symm y v v| ≤
          epsilon * (G.limit.flow.metric t).pullbackCoefficients
            (extChartAt (𝓡 3) q).symm y v v := by
  have hconv : TendstoUniformlyOn
      (fun i => coordinateRicci (comparisonConnection G t (sigma i))
        (comparisonChart G q t (sigma i) (htime i)))
      (coordinateRicci (G.limit.flow.connection t) (extChartAt (𝓡 3) q).symm) atTop K := by
    apply Poincare.Analysis.Calculus.tendstoUniformlyOn_bilinear_of_basis_entries
    intro a b
    exact tendstoUniformlyOn_ricci_of_scalar_pullback_jets
      (fun i => comparisonMetric G t (sigma i))
      (fun i => comparisonConnection G t (sigma i))
      (fun i => comparisonChart G q t (sigma i) (htime i))
      (G.limit.flow.metric t) (G.limit.flow.connection t) (extChartAt (𝓡 3) q).symm
      hK (isOpen_extChartAt_target q) hKc (contMDiffOn_extChartAt_symm q)
      (fun _ hy => Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hy)
      (comparisonChart_domains G q hK hKc sigma hsigma htime)
      (fun r _ a b => blowup_tendstoUniformlyOn_slice_pullbackJet
        G ht q hK hKc sigma hsigma htime r a b)
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
  exact eventually_bilinear_quadratic_error_le hK
    (((G.limit.flow.metric t).contDiffOn_chartCoefficients q).continuousOn.mono hKc)
    (fun y hy v hv => comparison_chart_metric_positive G q t (hKc hy) v hv) hconv hepsilon

private theorem comparison_chart_scalar
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (q : G.limit.carrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (htime : ∀ i, t ∈ Icc (-G.exhaustion.time (sigma i)) 0) :
    TendstoUniformlyOn
      (fun i y => (comparisonConnection G t (sigma i)).scalarCurvature
        (comparisonChart G q t (sigma i) (htime i) y))
      (fun y => (G.limit.flow.connection t).scalarCurvature
        ((extChartAt (𝓡 3) q).symm y)) atTop K := by
  let B := fun i => (comparisonMetric G t (sigma i)).pullbackCoefficients
    (comparisonChart G q t (sigma i) (htime i))
  let C := (G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm
  have hdom := comparisonChart_domains G q hK hKc sigma hsigma htime
  have hB : ∀ᶠ i in atTop, ∀ y ∈ K, ContDiffAt ℝ ∞ (B i) y := by
    filter_upwards [hdom] with i hi y hy
    obtain ⟨V, hV, hKV, hs, _⟩ := hi
    exact (comparisonMetric G t (sigma i)).contDiffAt_pullbackCoefficients
      (hs.contMDiffAt (hV.mem_nhds (hKV hy)))
  have hC (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ K) : ContDiffAt ℝ ∞ C y :=
    (G.limit.flow.metric t).contDiffAt_pullbackCoefficients
      ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target q).mem_nhds (hKc hy)))
  have htwo : TendstoUniformlyOn (fun i => metricTwoJet (B i)) (metricTwoJet C) atTop K :=
    tendstoUniformlyOn_metricTwoJet_of_bilinear_jets fun r _ =>
      tendstoUniformlyOn_bilinear_metricJet_of_scalar_entries hB hC fun a b =>
        blowup_tendstoUniformlyOn_slice_pullbackJet G ht q hK hKc sigma hsigma htime r a b
  have hcont : ContinuousOn (metricTwoJet C) K := by
    intro y hy
    have hfirst := (hC y hy).fderiv_right (m := ∞) (by simp)
    have hsecond := hfirst.fderiv_right (m := ∞) (by simp)
    exact ((hC y hy).continuousAt.prodMk
      (hfirst.continuousAt.prodMk hsecond.continuousAt)).continuousWithinAt
  have hscalar : TendstoUniformlyOn
      (fun i y => scalarMetricTraceTwoJet (metricTwoJet (B i) y))
      (fun y => scalarMetricTraceTwoJet (metricTwoJet C y)) atTop K := by
    apply tendstoUniformlyOn_comp_of_isCompact_image
      (g := scalarMetricTraceTwoJet) (hK.image_of_continuousOn hcont) ?_ htwo
    rintro jet ⟨y, hy, rfl⟩
    exact (contDiffAt_scalarMetricTraceTwoJet
      ((G.limit.flow.metric t).isInvertible_chartCoefficients q (hKc hy))).continuousAt
  have hlim := hscalar.congr_right
    (g := fun y => (G.limit.flow.connection t).scalarCurvature ((extChartAt (𝓡 3) q).symm y))
    (fun y hy => scalarMetricTraceTwoJet_pullback (G.limit.flow.connection t)
      (isOpen_extChartAt_target q) (contMDiffOn_extChartAt_symm q)
      (fun _ hz => Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hz)
      (hKc hy))
  apply hlim.congr
  filter_upwards [hdom] with i hi y hy
  obtain ⟨V, hV, hKV, hs, hinv⟩ := hi
  exact scalarMetricTraceTwoJet_pullback (comparisonConnection G t (sigma i))
    hV hs hinv (hKV hy)

private theorem comparison_chart_metric
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (q : G.limit.carrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (htime : ∀ i, t ∈ Icc (-G.exhaustion.time (sigma i)) 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ i in atTop, ∀ y ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3),
      |(comparisonMetric G t (sigma i)).pullbackCoefficients
          (comparisonChart G q t (sigma i) (htime i)) y v v -
        (G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm y v v| ≤
          epsilon * (G.limit.flow.metric t).pullbackCoefficients
            (extChartAt (𝓡 3) q).symm y v v := by
  have hconv : TendstoUniformlyOn
      (fun i => (comparisonMetric G t (sigma i)).pullbackCoefficients
        (comparisonChart G q t (sigma i) (htime i)))
      ((G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm) atTop K := by
    apply Poincare.Analysis.Calculus.tendstoUniformlyOn_bilinear_of_basis_entries
    intro a b
    have h := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (F := ℝ) (0 : Fin 0 → EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn
        (blowup_tendstoUniformlyOn_slice_pullbackJet G ht q hK hKc sigma hsigma htime 0 a b)
    simpa only [comparisonMetric, comparisonChart, Function.comp_def,
      iteratedFDeriv_zero_apply] using h
  exact eventually_bilinear_quadratic_error_le hK
    (((G.limit.flow.metric t).contDiffOn_chartCoefficients q).continuousOn.mono hKc)
    (fun y hy v hv => comparison_chart_metric_positive G q t (hKc hy) v hv) hconv hepsilon

private theorem comparison_chart_inverse
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    {x : G.limit.carrier.carrier} (hx : x ∈ (extChartAt (𝓡 3) q).source)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm (extChartAt (𝓡 3) q x)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q) x v) = v := by
  have h := congrArg (fun B => B v)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
    ContinuousLinearMap.comp_apply] at h
  exact h

private theorem comparisonChart_mfderiv_apply
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    {t : ℝ} (k : ℕ) (htk : t ∈ Icc (-G.exhaustion.time k) 0)
    {x : G.limit.carrier.carrier} (hx : x ∈ (extChartAt (𝓡 3) q).source)
    (hxk : x ∈ G.exhaustion.space k) (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (comparisonChart G q t k htk) (extChartAt (𝓡 3) q x)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q) x v) =
        mfderiv (𝓡 3) (𝓡 3) ((G.embedding k).forward t htk) x v := by
  let c := extChartAt (𝓡 3) q
  have hxk' : c.symm (c x) ∈ G.exhaustion.space k := (c.left_inv hx).symm ▸ hxk
  have hf := ((G.embedding k).forward_smooth t htk).contMDiffAt
    ((G.exhaustion.space_open k).mem_nhds hxk')
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds (c.map_source hx))
  rw [comparisonChart, mfderiv_comp _ (hf.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))]
  change mfderiv (𝓡 3) (𝓡 3) ((G.embedding k).forward t htk) (c.symm (c x))
    (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v)) = _
  erw [comparison_chart_inverse G q hx v, c.left_inv hx]

private theorem comparison_chart_inner
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier) (t : ℝ)
    {x : G.limit.carrier.carrier} (hx : x ∈ (extChartAt (𝓡 3) q).source)
    (v : TangentSpace (𝓡 3) x) :
    (G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm
      (extChartAt (𝓡 3) q x)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q) x v)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q) x v) =
        (G.limit.flow.metric t).inner x v v := by
  change (G.limit.flow.metric t).inner ((extChartAt (𝓡 3) q).symm
    (extChartAt (𝓡 3) q x)) _ _ = _
  erw [comparison_chart_inverse G q hx v, (extChartAt (𝓡 3) q).left_inv hx]

private theorem eventually_on_compact_of_coordinate_sets
    (G : GeneralizedBlowupConvergence S J) {K : Set G.limit.carrier.carrier}
    (hK : IsCompact K) {P : ℕ → G.limit.carrier.carrier → Prop}
    (hchart : ∀ q : G.limit.carrier.carrier,
      ∀ D : Set (EuclideanSpace ℝ (Fin 3)), IsCompact D →
        D ⊆ (extChartAt (𝓡 3) q).target →
        ∀ᶠ i in atTop, ∀ x, x ∈ (extChartAt (𝓡 3) q).source →
          extChartAt (𝓡 3) q x ∈ D → P i x) :
    ∀ᶠ i in atTop, ∀ x ∈ K, P i x := by
  apply hK.induction_on (p := fun A => ∀ᶠ i in atTop, ∀ x ∈ A, P i x)
  · exact Eventually.of_forall (by simp)
  · intro A B hAB hB
    exact hB.mono fun i hi x hx => hi x (hAB hx)
  · intro A B hA hB
    filter_upwards [hA, hB] with i hiA hiB x hx
    exact hx.elim (hiA x) (hiB x)
  · intro q _
    let c := extChartAt (𝓡 3) q
    obtain ⟨r, hr, hrc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (mem_extChartAt_target q))
    let V := c.source ∩ c ⁻¹' Metric.ball (c q) r
    have hV : V ∈ 𝓝 q := inter_mem (extChartAt_source_mem_nhds q)
      ((continuousAt_extChartAt q).preimage_mem_nhds (Metric.ball_mem_nhds (c q) hr))
    refine ⟨V, mem_nhdsWithin_of_mem_nhds hV, ?_⟩
    filter_upwards [hchart q (Metric.closedBall (c q) r)
      (isCompact_closedBall (c q) r) hrc] with i hi x hx
    exact hi x hx.1 (Metric.ball_subset_closedBall hx.2)

private theorem comparison_shift_tendsto (k0 : ℕ) :
    Tendsto (fun i : ℕ => k0 + i) atTop atTop :=
  tendsto_atTop.mpr fun N => (eventually_ge_atTop N).mono fun _ hi => by omega

private theorem eventually_slice_comparison
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {P : ∀ k, t ∈ Icc (-G.exhaustion.time k) 0 → G.limit.carrier.carrier → Prop}
    (hshift : ∀ (k0 : ℕ) (htime : ∀ i, t ∈ Icc (-G.exhaustion.time (k0 + i)) 0),
      ∀ᶠ i in atTop, ∀ x ∈ K, P (k0 + i) (htime i) x) :
    ∀ᶠ k in atTop, ∃ htk : t ∈ Icc (-G.exhaustion.time k) 0,
      K ⊆ G.exhaustion.space k ∧ ∀ x ∈ K, P k htk x := by
  have htime' : ∀ᶠ k in atTop, t ∈ Icc (-G.exhaustion.time k) 0 :=
    (G.exhaustion.time_cofinal {t} isCompact_singleton (singleton_subset_iff.mpr ht)).mono
      fun _ hk => hk (mem_singleton t)
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp htime'
  let htime := fun i : ℕ => hk0 (k0 + i) (Nat.le_add_right k0 i)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hshift k0 htime)
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G hK
  filter_upwards [eventually_ge_atTop (max j (k0 + N))] with k hk
  have hkbase : k0 ≤ k := by omega
  refine ⟨hk0 k hkbase, fun _ hx => G.exhaustion.space_increasing (by omega) (hj hx), ?_⟩
  intro x hx
  have h := hN (k - k0) (by omega) x hx
  have heq : k0 + (k - k0) = k := by omega
  simpa only [heq] using h

theorem blowup_eventually_sliceRicci_error
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop, ∃ htk : t ∈ Icc (-G.exhaustion.time k) 0,
      K ⊆ G.exhaustion.space k ∧ ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        |((S.flow (G.subsequence k)).connection
            ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).ricci
              ((G.embedding k).forward t htk x)
              (mfderiv (𝓡 3) (𝓡 3) ((G.embedding k).forward t htk) x v)
              (mfderiv (𝓡 3) (𝓡 3) ((G.embedding k).forward t htk) x v) -
          (G.limit.flow.connection t).ricci x v v| ≤
            epsilon * (G.limit.flow.metric t).inner x v v := by
  apply eventually_slice_comparison G ht hK
  intro k0 htime
  apply eventually_on_compact_of_coordinate_sets G hK
  intro q D hD hDc
  let c := extChartAt (𝓡 3) q
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G
    (hD.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hDc))
  filter_upwards [comparison_chart_Ricci G ht q hD hDc (fun i => k0 + i)
    (comparison_shift_tendsto k0) htime hepsilon,
    (comparison_shift_tendsto k0).eventually (eventually_ge_atTop j)] with i hi hij x hx hxD v
  have hxk : x ∈ G.exhaustion.space (k0 + i) := by
    have h := G.exhaustion.space_increasing hij (hj (mem_image_of_mem _ hxD))
    change c.symm (c x) ∈ G.exhaustion.space (k0 + i) at h
    rwa [c.left_inv hx] at h
  have h := hi (c x) hxD (mfderiv (𝓡 3) (𝓡 3) c x v)
  rw [comparison_chart_inner G q t hx v] at h
  change |(comparisonConnection G t (k0 + i)).ricci
    (comparisonChart G q t (k0 + i) (htime i) (c x))
    (mfderiv (𝓡 3) (𝓡 3) (comparisonChart G q t (k0 + i) (htime i)) (c x)
      (mfderiv (𝓡 3) (𝓡 3) c x v))
    (mfderiv (𝓡 3) (𝓡 3) (comparisonChart G q t (k0 + i) (htime i)) (c x)
      (mfderiv (𝓡 3) (𝓡 3) c x v)) -
    (G.limit.flow.connection t).ricci (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x v))| ≤ _ at h
  erw [comparisonChart_mfderiv_apply G q (k0 + i) (htime i) hx hxk v,
    comparison_chart_inverse G q hx v, c.left_inv hx] at h
  have hmap : comparisonChart G q t (k0 + i) (htime i) (c x) =
      (G.embedding (k0 + i)).forward t (htime i) x :=
    congrArg ((G.embedding (k0 + i)).forward t (htime i)) (c.left_inv hx)
  erw [hmap] at h
  simpa only [comparisonConnection, rescaledMetric_ricci] using h

theorem blowup_eventually_sliceScalar_error
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop, ∃ htk : t ∈ Icc (-G.exhaustion.time k) 0,
      K ⊆ G.exhaustion.space k ∧ ∀ x ∈ K,
        |(S.flow (G.subsequence k)).scalar ((G.embedding k).pointMap t htk x) /
            S.scale (G.subsequence k) -
          (G.limit.flow.connection t).scalarCurvature x| < epsilon := by
  apply eventually_slice_comparison G ht hK
  intro k0 htime
  apply eventually_on_compact_of_coordinate_sets G hK
  intro q D hD hDc
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (comparison_chart_scalar G ht q hD hDc (fun i => k0 + i)
      (comparison_shift_tendsto k0) htime) epsilon hepsilon] with i hi x hx hxD
  have h := hi (extChartAt (𝓡 3) q x) hxD
  rw [dist_comm, Real.dist_eq] at h
  simpa only [comparisonChart, comparisonConnection, Function.comp_apply,
    (extChartAt (𝓡 3) q).left_inv hx, rescaledMetric_scalarCurvature,
    GeneralizedRicciFlowData.scalar, GeneralizedFlowCylinder.pointMap,
    div_eq_mul_inv, mul_comm] using h

theorem blowup_eventually_sliceMetric_error
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop, ∃ htk : t ∈ Icc (-G.exhaustion.time k) 0,
      K ⊆ G.exhaustion.space k ∧ ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        |(G.embedding k).pullbackInner t htk x v v - (G.limit.flow.metric t).inner x v v| ≤
          epsilon * (G.limit.flow.metric t).inner x v v := by
  apply eventually_slice_comparison G ht hK
  intro k0 htime
  apply eventually_on_compact_of_coordinate_sets G hK
  intro q D hD hDc
  let c := extChartAt (𝓡 3) q
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G
    (hD.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hDc))
  filter_upwards [comparison_chart_metric G ht q hD hDc (fun i => k0 + i)
    (comparison_shift_tendsto k0) htime hepsilon,
    (comparison_shift_tendsto k0).eventually (eventually_ge_atTop j)] with i hi hij x hx hxD v
  have hxk : x ∈ G.exhaustion.space (k0 + i) := by
    have h := G.exhaustion.space_increasing hij (hj (mem_image_of_mem _ hxD))
    change c.symm (c x) ∈ G.exhaustion.space (k0 + i) at h
    rwa [c.left_inv hx] at h
  have h := hi (c x) hxD (mfderiv (𝓡 3) (𝓡 3) c x v)
  rw [comparison_chart_inner G q t hx v] at h
  change |(comparisonMetric G t (k0 + i)).inner
    (comparisonChart G q t (k0 + i) (htime i) (c x))
    (mfderiv (𝓡 3) (𝓡 3) (comparisonChart G q t (k0 + i) (htime i)) (c x)
      (mfderiv (𝓡 3) (𝓡 3) c x v))
    (mfderiv (𝓡 3) (𝓡 3) (comparisonChart G q t (k0 + i) (htime i)) (c x)
      (mfderiv (𝓡 3) (𝓡 3) c x v)) - (G.limit.flow.metric t).inner x v v| ≤ _ at h
  erw [comparisonChart_mfderiv_apply G q (k0 + i) (htime i) hx hxk v] at h
  have hmap : comparisonChart G q t (k0 + i) (htime i) (c x) =
      (G.embedding (k0 + i)).forward t (htime i) x :=
    congrArg ((G.embedding (k0 + i)).forward t (htime i)) (c.left_inv hx)
  erw [hmap] at h
  simpa only [comparisonMetric, rescaledMetric_inner,
    GeneralizedFlowCylinder.pullbackInner] using h

end PoincareConjecture.M32
