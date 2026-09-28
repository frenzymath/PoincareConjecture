import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.CoefficientRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.SquareTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MetricPair








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

section Coordinate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local instance localDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance localDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance localBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance localBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance localEndGroup : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance localEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

private theorem exists_smooth_linear_transport
    (A : ℝ → E →L[ℝ] E) {a b s₀ : ℝ} (hs₀ : s₀ ∈ Ioo a b)
    (hA : ContDiffOn ℝ ∞ A (Ioo a b)) {ι : Type*} (e : ι → E) :
    ∃ v : ι → ℝ → E,
      (∀ i, ContDiffOn ℝ ∞ (v i) (Ioo a b)) ∧
      (∀ i, v i s₀ = e i) ∧
      (∀ i s, s ∈ Ioo a b → HasDerivAt (v i) (A s (v i s)) s) := by
  let B : ℝ → ℝ → E →L[ℝ] E := fun _ s ↦ A s
  have hB : ContDiffOn ℝ ∞ (Function.uncurry B) (univ ×ˢ Ioo a b) :=
    hA.comp contDiffOn_snd (fun _ hz ↦ hz.2)
  let v : ι → ℝ → E := fun i ↦
    Poincare.ODE.LocalFlow.linearODESolution B a b s₀ (fun _ ↦ e i) 0
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    have h := Poincare.ODE.LocalFlow.linearODESolution_contDiffOn_top
      (A := B) (Z₀ := fun _ ↦ e i) hs₀ isOpen_univ hB contDiffOn_const
    exact h.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun s hs ↦ ⟨mem_univ (0 : ℝ), hs⟩)
  · intro i
    exact Poincare.ODE.LocalFlow.linearODESolution_init _ _ _ _ _ _
  · intro i s hs
    exact Poincare.ODE.LocalFlow.linearODESolution_hasDerivAt
      (A := B) (Z₀ := fun _ ↦ e i) hs₀ hB.continuousOn (mem_univ (0 : ℝ)) hs

private theorem metricAlong_hasDerivAt
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (y u v : ℝ → E) (s : ℝ)
    (a u' v' : E) (hG : DifferentiableAt ℝ G (s, y s))
    (hy : HasDerivAt y a s) (hu : HasDerivAt u u' s) (hv : HasDerivAt v v' s) :
    HasDerivAt (fun t ↦ G (t, y t) (u t) (v t))
      (fderiv ℝ G (s, y s) (1, a) (u s) (v s) +
        G (s, y s) u' (v s) + G (s, y s) (u s) v') s := by
  have hc := hG.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk hy)
  have hp := (hc.clm_apply hu).clm_apply hv
  simpa only [Function.comp_def, id_eq, add_apply] using hp

set_option backward.isDefEq.respectTransparency true in
theorem exists_smooth_coordinate_transport
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (U : Set (ℝ × E))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (hsym : ∀ z ∈ U, ∀ v w, G z v w = G z w v)
    (y : ℝ → E) {a b s₀ : ℝ} (hs₀ : s₀ ∈ Ioo a b)
    (hy : ContDiffOn ℝ ∞ y (Ioo a b))
    (hgraph : ∀ s ∈ Ioo a b, (s, y s) ∈ U)
    {ι : Type*} (e : ι → E) :
    ∃ v : ι → ℝ → E,
      (∀ i, ContDiffOn ℝ ∞ (v i) (Ioo a b)) ∧
      (∀ i, v i s₀ = e i) ∧
      (∀ i s, s ∈ Ioo a b → HasDerivAt (v i)
        (chartTransportOperator G (s, y s) (deriv y s) (v i s)) s) ∧
      (∀ i j s, s ∈ Ioo a b →
        G (s, y s) (v i s) (v j s) = G (s₀, y s₀) (e i) (e j)) := by
  let A : ℝ → E →L[ℝ] E := fun s ↦ chartTransportOperator G (s, y s) (deriv y s)
  have hy' : ContDiffOn ℝ ∞ (deriv y) (Ioo a b) :=
    hy.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)
  have hA : ContDiffOn ℝ ∞ A (Ioo a b) :=
    (chartTransportOperator_contDiffOn G U hU hG hpos).comp
      (f := fun s : ℝ ↦ ((s, y s), deriv y s))
      ((contDiffOn_id.prodMk hy).prodMk hy') (fun s hs ↦ ⟨hgraph s hs, mem_univ _⟩)
  obtain ⟨v, hv, hv₀, hderiv⟩ := exists_smooth_linear_transport A hs₀ hA e
  refine ⟨v, hv, hv₀, hderiv, ?_⟩
  intro i j s hs
  have hpair (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt (fun t ↦ G (t, y t) (v i t) (v j t)) 0 r := by
    have hGr := ((hG _ (hgraph r hr)).contDiffAt
      (hU.mem_nhds (hgraph r hr))).differentiableAt (by simp)
    have hyr := ((hy r hr).contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)
    have hp := metricAlong_hasDerivAt G y (v i) (v j) r
      (deriv y r) (A r (v i r)) (A r (v j r)) hGr hyr.hasDerivAt
        (hderiv i r hr) (hderiv j r hr)
    have hsymr : ∀ᶠ z in 𝓝 (r, y r), ∀ u w, G z u w = G z w u := by
      filter_upwards [hU.mem_nhds (hgraph r hr)] with z hz
      exact hsym z hz
    have hzero := chartTransportOperator_metric_identity G (r, y r) hGr hsymr
      (hpos _ (hgraph r hr)) (deriv y r) (v i r) (v j r)
    apply hp.congr_deriv
    exact hzero
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero
    (f := fun t ↦ G (t, y t) (v i t) (v j t)) (convex_Ioo a b).isPreconnected
    (fun r hr ↦ (hpair r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hpair r hr).deriv) hs hs₀
  simpa only [hv₀] using heq

end Coordinate

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)




theorem exists_smooth_adapted_orthonormal_chart_frame
    {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M) (γ : ℝ → M)
    {a b s₀ : ℝ} (hs₀ : s₀ ∈ Ioo a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo a b))
    (hchart : ∀ s ∈ Ioo a b, γ s ∈ (chartAt E x).source)
    (htime : ∀ s ∈ Ioo a b, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J)) :
    ∃ v : Fin n → ℝ → E,
      (∀ i, ContDiffOn ℝ ∞ (v i) (Ioo a b)) ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
        (fun s ↦ Bundle.TotalSpace.mk' E (γ s) (chartFrame x (v i s) (γ s))) (Ioo a b)) ∧
      (∀ i j s, s ∈ Ioo a b →
        (F.metric (T - s ^ 2)).inner (γ s) (chartFrame x (v i s) (γ s))
          (chartFrame x (v j s) (γ s)) = if i = j then 1 else 0) ∧
      (∀ i s, s ∈ Ioo a b → ∀ Z : TangentSpace (𝓡 n) (γ s),
        (F.metric (T - s ^ 2)).inner (γ s)
          (chartFrame x (deriv (v i) s) (γ s) +
            (F.connection (T - s ^ 2)).connection (chartFrame x (v i s)) (γ s)
              (curveVelocity γ s)) Z =
          -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s)
            (chartFrame x (v i s) (γ s)) Z) := by
  classical
  let y : ℝ → E := fun s ↦ extChartAt (𝓡 n) x (γ s)
  have hy : ContDiffOn ℝ ∞ y (Ioo a b) := by
    apply ContMDiffOn.contDiffOn
    exact (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp hγ (fun s hs ↦ by
      simpa only [extChartAt_source, mem_preimage] using hchart s hs)
  have hgraph (s : ℝ) (hs : s ∈ Ioo a b) : (s, y s) ∈ chartActionDomain F T x :=
    ⟨htime s hs, (extChartAt (𝓡 n) x).map_source (by
      simpa only [extChartAt_source] using hchart s hs)⟩
  let g := F.metric (T - s₀ ^ 2)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let e := trivializationAt E (TangentSpace (𝓡 n)) x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) (γ s₀)) = n := finrank_euclideanSpace_fin
  let B : Fin n → TangentSpace (𝓡 n) (γ s₀) :=
    fun i ↦ g.orthonormalBasis (γ s₀) (Fin.cast hdim.symm i)
  let v₀ : Fin n → E := fun i ↦ e.continuousLinearMapAt ℝ (γ s₀) (B i)
  have hv₀ (i : Fin n) : chartFrame x (v₀ i) (γ s₀) = B i :=
    e.symmL_continuousLinearMapAt (hchart s₀ hs₀) (B i)
  have horth (i j : Fin n) :
      chartActionMetric F T x (s₀, y s₀) (v₀ i) (v₀ j) = if i = j then 1 else 0 := by
    rw [chartActionMetric_apply F T (hchart s₀ hs₀), hv₀ i, hv₀ j]
    change inner ℝ (g.orthonormalBasis (γ s₀) (Fin.cast hdim.symm i))
      (g.orthonormalBasis (γ s₀) (Fin.cast hdim.symm j)) = _
    simpa using (g.orthonormalBasis (γ s₀)).inner_eq_ite
      (Fin.cast hdim.symm i) (Fin.cast hdim.symm j)
  obtain ⟨v, hv, _, hd, hpair⟩ := exists_smooth_coordinate_transport
    (chartActionMetric F T x) (chartActionDomain F T x)
    (chartActionDomain_open F T x) (chartActionMetric_contDiffOn F T x)
    (fun z hz ↦ chartActionMetric_pos F T x hz)
    (fun z hz ↦ chartActionMetric_symm F T x hz) y hs₀ hy hgraph v₀
  refine ⟨v, hv, (fun i ↦ chartFrame_curve_contMDiffOn x γ (v i) _ hγ (hv i) hchart), ?_, ?_⟩
  · intro i j s hs
    rw [← chartActionMetric_apply F T (hchart s hs)]
    exact (hpair i j s hs).trans (horth i j)
  · intro i s hs Z
    have hγs := ((hγ s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt (by simp)
    rw [(hd i s hs).deriv, ← chartFrame_curveVelocity (hchart s hs) hγs]
    exact chartTransportOperator_adapted_pairing_squareDomain F T s x (γ s)
      (hchart s hs) (htime s hs) (deriv y s) (v i s) Z

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
