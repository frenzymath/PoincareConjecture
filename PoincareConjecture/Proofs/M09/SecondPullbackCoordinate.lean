import PoincareConjecture.Proofs.M09.PullbackCoordinate

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem coordinateFieldDerivative_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hq : ∀ s ∈ U, γ s ∈ (chartAt V p).source)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (v : ℝ → V) (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (fun s ↦ deriv v s +
      coordinateConnection (squareChartMetric F T p) (s, (chartAt V p) (γ s))
        (deriv (fun r ↦ (chartAt V p) (γ r)) s) (v s)) U := by
  let a : ℝ → V := fun s ↦ (chartAt V p) (γ s)
  have ha : ContDiffOn ℝ ∞ a U := (contMDiffOn_chart.comp hγ hq).contDiffOn
  have hC := coordinateConnection_smooth (squareChartMetric F T p)
    (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt V p).target)
    (isOpen_Ioo.prod (chartAt V p).open_target)
    (squareChartMetric_smooth F T b hb hwindow p)
    (fun z hz w hw ↦ squareChartMetric_pos F T p z hz.2 w hw)
  have hmap : ContDiffOn ℝ ∞ (fun s ↦ ((s, a s), (deriv a s, v s))) U :=
    (contDiffOn_id.prodMk ha).prodMk ((ha.deriv_of_isOpen hU (by simp)).prodMk hv)
  have hmaps : Set.MapsTo (fun s ↦ ((s, a s), (deriv a s, v s))) U
      {q : (ℝ × V) × (V × V) |
        q.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt V p).target} :=
    fun s hs ↦ ⟨htime hs, (chartAt V p).map_source (hq s hs)⟩
  have hc := hC.comp hmap hmaps
  exact (hv.deriv_of_isOpen hU (by simp)).add hc

theorem repeatedPullbackCovariantDerivative_eq_chart {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (γ : ℝ → M) (Y : ∀ s, TangentSpace (𝓡 n) (γ s))
    (K U : Set ℝ) (E : ParametricAlongCurveExtensionOn K γ Y)
    (E2 : ParametricAlongCurveExtensionOn K γ
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ Y K E))
    (hU : IsOpen U) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hq : ∀ s ∈ U, γ s ∈ (chartAt V p).source)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (hKd : UniqueDiffOn ℝ K)
    (v : ℝ → V) (hv : ContDiffOn ℝ ∞ v U)
    (heq : ∀ s ∈ K ∩ U, chartVectorField p (v s) (γ s) = Y s)
    (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U) :
    let a : ℝ → V := fun r ↦ (chartAt V p) (γ r)
    let d : ℝ → V := fun r ↦ deriv v r +
      coordinateConnection (squareChartMetric F T p) (r, a r) (deriv a r) (v r)
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ Y K E) K E2 s =
        chartVectorField p (deriv d s + coordinateConnection (squareChartMetric F T p)
          (s, a s) (deriv a s) (d s)) (γ s) := by
  let a : ℝ → V := fun r ↦ (chartAt V p) (γ r)
  let d : ℝ → V := fun r ↦ deriv v r +
    coordinateConnection (squareChartMetric F T p) (r, a r) (deriv a r) (v r)
  have hd : ContDiffOn ℝ ∞ d U :=
    coordinateFieldDerivative_contDiffOn F T b hb hwindow p γ U hU hγ hq htime v hv
  have hfirst (r : ℝ) (hr : r ∈ K ∩ U) :
      chartVectorField p (d r) (γ r) =
        pullbackCovariantDerivative F (fun t ↦ T - t ^ 2) γ Y K E r :=
    (pullbackCovariantDerivative_eq_chart F T b hb hwindow p γ Y K U E
      hU hγ hq v hv heq r hr.1 hr.2 (hKd r hr.1) (htime hr.2)).symm
  exact pullbackCovariantDerivative_eq_chart F T b hb hwindow p γ _ K U E2
    hU hγ hq d hd hfirst s hs hsU (hKd s hs) (htime hsU)

theorem sqrtRegularField_secondDerivative_eq_chart {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b} (τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (R : SqrtRegularPath p)
    (Y : ∀ t, TangentSpace (𝓡 n) (p.curve t)) (Q : SqrtRegularField R Y)
    (x0 : M) (U : Set ℝ) (hU : IsOpen U) (hUR : U ⊆ R.domain)
    (hq : ∀ s ∈ U, R.curve s ∈ (chartAt V x0).source)
    (htime : U ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (v : ℝ → V) (hv : ContDiffOn ℝ ∞ v U)
    (heq : ∀ s ∈ sqrtParameterInterval a b ∩ U,
      chartVectorField x0 (v s) (R.curve s) = Q.field s)
    (s : ℝ) (hs : s ∈ sqrtParameterInterval a b) (hsU : s ∈ U) :
    let c : ℝ → V := fun r ↦ (chartAt V x0) (R.curve r)
    let d : ℝ → V := fun r ↦ deriv v r +
      coordinateConnection (squareChartMetric F T x0) (r, c r) (deriv c r) (v r)
    Q.secondDerivative s = chartVectorField x0
      (deriv d s + coordinateConnection (squareChartMetric F T x0)
        (s, c s) (deriv c s) (d s)) (R.curve s) :=
  repeatedPullbackCovariantDerivative_eq_chart F T τmax hτmax hwindow x0 R.curve Q.field
    (sqrtParameterInterval a b) U Q.extension Q.derivative_extension hU (R.smooth.mono hUR)
    hq htime (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered))
    v hv heq s hs hsU

end PoincareConjecture.Proofs.M09
