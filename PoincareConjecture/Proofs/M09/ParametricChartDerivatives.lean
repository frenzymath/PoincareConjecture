import PoincareConjecture.Proofs.M09.ParametricScalarDerivatives
import PoincareConjecture.Proofs.M09.LocalFixedChartHessian
import PoincareConjecture.Proofs.M09.SquareChartConnection
import PoincareConjecture.Proofs.M09.CoordinateConnectionBilinear







set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {J : Set ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def parametricChartHessian (F : RicciFlow n M J) (T : ℝ) (p : M)
    (C : (P × E) × ℝ → ℝ) (z : (P × E) × ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  parametricSpatialSecond C z -
    ((ContinuousLinearMap.compL ℝ E E ℝ) (parametricSpatialCovector C z)).comp
      (coordinateConnectionBilinear (squareChartMetric F T p) (Real.sqrt z.2, z.1.2))

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem parametric_chart_derivatives (F : RicciFlow n M J) (T τmax : ℝ)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J) (p : M)
    (C : (P × E) × ℝ → ℝ) (U : Set ((P × E) × ℝ))
    (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U)
    (a : P) (y : E) (t : ℝ) (hy : y ∈ (chartAt E p).target)
    (ht : 0 < t) (hmax : t < τmax) (hz : ((a, y), t) ∈ U) :
    let e := chartAt E p
    let f : M × ℝ → ℝ := fun w ↦ C ((a, e w.1), w.2)
    (∀ u : E, mvfderiv (𝓡 n) (fun q ↦ f (q, t)) (e.symm y)
      (chartVectorField p u (e.symm y)) = parametricSpatialCovector C ((a, y), t) u) ∧
    (∀ u v : E, (F.connection (T - t)).hessian (fun q ↦ f (q, t))
      (e.symm y) (chartVectorField p u (e.symm y)) (chartVectorField p v (e.symm y)) =
        parametricChartHessian F T p C ((a, y), t) u v) ∧
    deriv (fun s ↦ f (e.symm y, s)) t = fderiv ℝ C ((a, y), t) ((0, 0), 1) := by
  dsimp only
  let e := chartAt E p
  let q := e.symm y
  let f : M → ℝ := fun x ↦ C ((a, e x), t)
  let c : M → (P × E) × ℝ := fun x ↦ ((a, e x), t)
  let O := e.source ∩ c ⁻¹' U
  have hc : ContMDiffOn (𝓡 n) (𝓘(ℝ, (P × E) × ℝ)) ∞ c e.source :=
    (contMDiffOn_const.prodMk_space contMDiffOn_chart).prodMk_space contMDiffOn_const
  have hO : IsOpen O := hc.continuousOn.isOpen_inter_preimage e.open_source hU
  have hqO : q ∈ O := ⟨e.map_target hy, by
    change ((a, e (e.symm y)), t) ∈ U
    rwa [e.right_inv hy]⟩
  have hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O :=
    hC.contMDiffOn.comp (hc.mono Set.inter_subset_left) (fun x hx ↦ hx.2)
  have hfd := (hf.contMDiffAt (hO.mem_nhds hqO)).mdifferentiableAt (by simp)
  let φ : E → ℝ := fun v ↦ f (e.symm v)
  let g : E → ℝ := fun v ↦ C ((a, v), t)
  have heq : φ =ᶠ[𝓝 y] g := by
    filter_upwards [e.open_target.mem_nhds hy] with v hv
    exact congrArg (fun w ↦ C ((a, w), t)) (e.right_inv hv)
  have heqD : fderiv ℝ φ =ᶠ[𝓝 y] fderiv ℝ g :=
    heq.eventuallyEq_nhds.mono (fun _ hh ↦ hh.fderiv_eq)
  have hCd := (hC.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hfirst : fderiv ℝ φ y = parametricSpatialCovector C ((a, y), t) :=
    heq.fderiv_eq.trans (fderiv_parametric_spatial_slice C a y t hCd)
  have hsecond : fderiv ℝ (fderiv ℝ φ) y = parametricSpatialSecond C ((a, y), t) :=
    heqD.fderiv_eq.trans (fderiv_parametric_spatial_second C U hU hC a y t hz)
  have hs : Real.sqrt t ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_neg_of_pos (Real.sqrt_pos.mpr hτmax)).trans_le (Real.sqrt_nonneg _),
      Real.sqrt_lt_sqrt ht.le hmax⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u
    exact (mvfderiv_chartVectorField_normed p f y u hy hfd).trans
      (congrArg (fun L : E →L[ℝ] ℝ ↦ L u) hfirst)
  · intro u v
    let A := coordinateConnectionBilinear (squareChartMetric F T p) (Real.sqrt t, y) u
    have hA (w : E) : (F.connection (T - t)).connection (chartVectorField p w)
        q (chartVectorField p u q) = chartVectorField p (A w) q := by
      have h := (squareChartConnection_eq F T τmax hτmax hwindow p (Real.sqrt t)
        hs y hy u w).symm
      have hsquare : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
      rw [hsquare] at h
      exact h
    have h := hessian_fixedChart_local (F.connection (T - t)) f p q (e.map_target hy)
      O hO hqO hf u v A hA
    change _ = fderiv ℝ (fderiv ℝ φ) (e q) u v - fderiv ℝ φ (e q) (A v) at h
    rw [show e q = y from e.right_inv hy, hfirst, hsecond] at h
    exact h
  · change deriv (fun s ↦ C ((a, e (e.symm y)), s)) t = _
    rw [e.right_inv hy]
    exact deriv_parametric_time_slice C a y t hCd

theorem parametricChartHessian_smooth (F : RicciFlow n M J) (T τmax : ℝ)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J) (p : M)
    (C : (P × E) × ℝ → ℝ) (U : Set ((P × E) × ℝ))
    (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (parametricChartHessian F T p C)
      (U ∩ ((Set.univ ×ˢ (chartAt E p).target) ×ˢ Set.Ioo 0 τmax)) := by
  let S := U ∩ ((Set.univ ×ˢ (chartAt E p).target) ×ˢ Set.Ioo 0 τmax)
  let V := Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ×ˢ (chartAt E p).target
  have hV : IsOpen V := isOpen_Ioo.prod (chartAt E p).open_target
  have hG := squareChartMetric_smooth F T τmax hτmax hwindow p
  have hK := coordinateConnectionBilinear_contDiffOn (squareChartMetric F T p) V hV hG
    (fun z hz u hu ↦ squareChartMetric_pos F T p z hz.2 u hu)
  have hi : ContDiffOn ℝ ∞ (fun z : (P × E) × ℝ ↦ (Real.sqrt z.2, z.1.2)) S :=
    (contDiffOn_snd.sqrt (fun z hz ↦ hz.2.2.1.ne')).prodMk contDiff_fst.snd.contDiffOn
  have hK' := hK.comp hi (fun z hz ↦
    ⟨⟨(neg_neg_of_pos (Real.sqrt_pos.mpr hτmax)).trans_le (Real.sqrt_nonneg _),
      Real.sqrt_lt_sqrt hz.2.2.1.le hz.2.2.2⟩, hz.2.1.2⟩)
  have hL : ContDiffOn ℝ ∞ (parametricSpatialCovector C) S :=
    (parametricSpatialCovector_smooth C U hU hC).mono Set.inter_subset_left
  exact ((parametricSpatialSecond_smooth C U hU hC).mono Set.inter_subset_left).sub
    ((contDiffOn_const.clm_apply hL).clm_comp hK')

end PoincareConjecture.Proofs.M09
