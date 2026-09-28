import PoincareConjecture.Proofs.M09.CenteredJacobiResidual
import PoincareConjecture.Proofs.M09.VariationChartField
import PoincareConjecture.Proofs.M09.FamilyLinearization
import PoincareConjecture.Proofs.M09.SecondPullbackCoordinate
import PoincareConjecture.Proofs.M09.InitialJacobiDerivative
import PoincareConjecture.Proofs.M09.InitialVariationDifferential

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_isLJacobiField
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    IsLJacobiField F T 0 b (A.path Z b hb hmax)
      (variationField (initialVectorVariation A Z W b hb hmax).toLVariation) := by
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  let R := lExponentialFamily_squareRegularization hM04 hτmax hwindow A Z b hb hmax
  let K := sqrtParameterInterval 0 b
  obtain ⟨Q⟩ := nonempty_sqrtRegularField_variation τmax hτmax hmax hwindow R.path V
  refine ⟨R, Q, initialVectorVariation_field_zero A Z W b hb hmax, ?_⟩
  intro s hs Wtest
  let x0 := R.path.curve s
  let H : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
  let Ω := V.squareDomain ∩ H ⁻¹' (chartAt E x0).source
  let U0 := (fun r : ℝ ↦ (r, (0 : ℝ))) ⁻¹' Ω
  let U := (U0 ∩ R.path.domain) ∩ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  let x : ℝ → E := fun r ↦ (chartAt E x0) (R.path.curve r)
  let v : ℝ → E := fun r ↦ deriv (fun u ↦ (chartAt E x0) (V.squareFamily r u)) 0
  let C := coordinateConnectionBilinear (squareChartMetric F T x0)
  let d : ℝ → E := fun r ↦ deriv v r + C (r, x r) (deriv x r) (v r)
  obtain ⟨hU0, hbase, hq0, hv0, hfield⟩ := squareVariationField_chart_smooth V x0
  have hbaseEq : V.baseSquareCurve = R.path.curve :=
    initialVectorVariation_baseSquareCurve A Z W b hb hmax
  have hx_eq : x = fun r ↦ (chartAt E x0) (A.squareFamily Z r) := rfl
  have hv_eq : v = fun r ↦
      deriv (fun u : ℝ ↦ (chartAt E x0) (A.squareFamily (Z + u • W) r)) 0 := by
    funext r
    simp only [v, V, initialVectorVariation_squareFamily]
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hsU0 : s ∈ U0 := by
    refine ⟨V.square_contains ⟨hs, neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩, ?_⟩
    change V.baseSquareCurve s ∈ (chartAt E x0).source
    rw [hbaseEq]
    exact mem_chart_source E x0
  have hU : IsOpen U := (hU0.inter R.path.open_domain).inter isOpen_Ioo
  have hsU : s ∈ U := ⟨⟨hsU0, R.path.interval_subset hs⟩, htime⟩
  have hUR : U ⊆ R.path.domain := fun _ hr ↦ hr.1.2
  have hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ R.path.curve U := R.path.smooth.mono hUR
  have hq : ∀ r ∈ U, R.path.curve r ∈ (chartAt E x0).source := by
    intro r hr
    rw [← hbaseEq]
    exact hq0 r hr.1.1
  have hv : ContDiffOn ℝ ∞ v U := hv0.mono (fun _ hr ↦ hr.1.1)
  have hx : ContDiffOn ℝ ∞ x U := (contMDiffOn_chart.comp hγ hq).contDiffOn
  have hcast (q q' : M) (h : q = q') (w : TangentSpace (𝓡 n) q) :
      (h ▸ w : TangentSpace (𝓡 n) q') = (show TangentSpace (𝓡 n) q' from w) := by
    cases h
    rfl
  have heq : ∀ r ∈ K ∩ U, chartVectorField x0 (v r) (R.path.curve r) = Q.field r := by
    intro r hr
    have hf := hfield r hr.2.1.1
    change (chartVectorField x0 (v r) (V.baseSquareCurve r) : E) = squareVariationField V r at hf
    rw [hbaseEq] at hf
    have hQ := Q.agrees r hr.1
    simp only [hcast] at hQ
    exact hf.trans ((squareVariationField_eq_variationField V r hr.1).trans hQ.symm)
  have hKd : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (by norm_num) hb)
  have hxAt := hx.contDiffAt (hU.mem_nhds hsU)
  have hvAt := hv.contDiffAt (hU.mem_nhds hsU)
  have hxd := hxAt.differentiableAt (by simp)
  have hvd := hvAt.differentiableAt (by simp)
  have hx2 := (hxAt.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hv2 := (hvAt.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hgd := (hγ.contMDiffAt (hU.mem_nhds hsU)).mdifferentiableAt (by simp)
  have hvel := (curveVelocityWithin_eq_curveVelocity R.path.curve K s (hKd s hs) hgd).trans
    (chartVectorField_coordinate_velocity x0 R.path.curve s (deriv x s) (hq s hsU) hgd
      hxd.hasDerivAt).symm
  have hvel' : (curveVelocityWithin (n := n) R.path.curve K s : E) = deriv x s := by
    have h := congrArg (fun z : TangentSpace (𝓡 n) (R.path.curve s) ↦ (z : E)) hvel
    simpa only [x0, chartVectorField_self] using h
  have hfield' : (Q.field s : E) = v s := by
    have h := congrArg (fun z : TangentSpace (𝓡 n) (R.path.curve s) ↦ (z : E))
      (heq s ⟨hs, hsU⟩).symm
    simpa only [x0, chartVectorField_self] using h
  have hfirst := pullbackCovariantDerivative_eq_chart F T τmax hτmax hwindow x0
    R.path.curve Q.field K U Q.extension hU hγ hq v hv heq s hs hsU (hKd s hs) htime
  have hfirst' : (Q.firstDerivative s : E) = d s := by
    have h := congrArg (fun z : TangentSpace (𝓡 n) (R.path.curve s) ↦ (z : E)) hfirst
    simpa only [SqrtRegularField.firstDerivative, d, C, x, x0,
      coordinateConnectionBilinear_apply, chartVectorField_self] using h
  have hsecond := sqrtRegularField_secondDerivative_eq_chart τmax hτmax hwindow R.path
    (variationField V) Q x0 U hU hUR hq (fun _ hr ↦ hr.2) v hv heq s hs hsU
  have hsecond' : (Q.secondDerivative s : E) =
      deriv d s + C (s, x s) (deriv x s) (d s) := by
    have h := congrArg (fun z : TangentSpace (𝓡 n) (R.path.curve s) ↦ (z : E)) hsecond
    simpa only [d, C, x, x0, coordinateConnectionBilinear_apply,
      chartVectorField_self] using h
  have hphase0 := lExponentialFamily_chartPhase_hasDerivAt hM04 hτmax hwindow A Z b hb hmax
    x0 s hs (mem_chart_source E x0)
  have hphase : deriv (deriv x) s =
      (regularizedCoordinatePhase (squareChartMetric F T x0) (squareChartScalar F T x0)
        (s, (x s, deriv x s))).2 := by
    have hd := (hphase0.hasFDerivAt.snd).hasDerivAt
    have hd' : HasDerivAt (deriv x)
        (regularizedCoordinatePhase (squareChartMetric F T x0) (squareChartScalar F T x0)
          (s, (x s, deriv x s))).2 s := by
      simpa [hx_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply] using hd
    exact hd'.deriv
  have hlin0 := lExponentialFamily_variation_phase_hasDerivAt hM04 hτmax hwindow A
    Z W b hb hmax x0 s hs (mem_chart_source E x0)
  dsimp only at hlin0
  simp only [timeDerivativePhase, zero_smul, add_zero] at hlin0
  have hlinear : deriv (deriv v) s =
      (fderiv ℝ (regularizedCoordinatePhase (squareChartMetric F T x0)
        (squareChartScalar F T x0)) (s, (x s, deriv x s)) (0, (v s, deriv v s))).2 := by
    have hd := (hlin0.hasFDerivAt.snd).hasDerivAt
    have hd' : HasDerivAt (deriv v)
        (fderiv ℝ (regularizedCoordinatePhase (squareChartMetric F T x0)
          (squareChartScalar F T x0)) (s, (x s, deriv x s)) (0, (v s, deriv v s))).2 s := by
      simpa [hx_eq, hv_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply] using hd
    exact hd'.deriv
  have hres := centered_coordinate_jacobi_residual F hM04 T τmax hτmax hwindow x0 x v s
    htime rfl hxd hx2 hvd hv2 hphase hlinear Wtest
  unfold regularizedJacobiResidual
  dsimp only
  rw [hvel', hfield', hfirst', hsecond']
  exact hres

theorem lExponentialFamily_jacobi_differential
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    ∃ Y : ∀ τ, TangentSpace (𝓡 n) ((A.path Z b hb hmax).curve τ),
      IsLJacobiField F T 0 b (A.path Z b hb hmax) Y ∧
      HasLJacobiInitialDerivative (A.regularization Z b hb hmax) Y
        (((congrFun (A.path_eq Z b hb hmax) 0).trans (A.gamma_at_zero Z)).symm ▸ ((2 : ℝ) • W)) ∧
      ∀ τ ∈ Set.Icc 0 b,
        ((congrFun (A.path_eq Z b hb hmax) τ) ▸ Y τ : TangentSpace (𝓡 n) (A.gamma Z τ)) =
          A.sliceDifferential Z τ W := by
  exact ⟨variationField (initialVectorVariation A Z W b hb hmax).toLVariation,
    initialVectorVariation_isLJacobiField hM04 hτmax hwindow A Z W b hb hmax,
    initialVectorVariation_hasLJacobiInitialDerivative hτmax hwindow A Z W b hb hmax,
    initialVectorVariation_differential_on_interval A Z W b hb hmax⟩

end PoincareConjecture.Proofs.M09
