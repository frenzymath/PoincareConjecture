import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerMaximalRank
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerRankGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerConcentration
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.AnnularBound







open Set Filter Topology MeasureTheory Function
open PoincareConjecture Poincare.GromovHausdorff Poincare.CurvatureIntegral Poincare.Alexandrov
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
private theorem corner_ascent_rates {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    ∃ cminus c cplus θ : ℝ,
      v < cminus ∧ cminus < c ∧ c < cplus ∧ cplus < 1 ∧
      0 ≤ c ∧ 0 < θ ∧ θ < Real.pi/2 ∧ c < Real.cos (2*θ) := by
  let d := 1-v
  have hd : 0 < d := sub_pos.mpr hv1
  have hd1 : d < 1 := by dsimp [d]; linarith
  refine ⟨1-d/2, 1-d/4, 1-d/8, d/16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [d]; linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · positivity
  · linarith [Real.pi_gt_three]
  · have hcos := Real.one_sub_sq_div_two_le_cos (x := 2*(d/16))
    nlinarith

theorem PoincareConjecture.exists_uniform_pointedCornerModel_scalar_bound_of_lower_dimensional_bound
    (m k : ℕ) (hm : 1 ≤ m) (Δ : ℝ) (hΔ : 0 < Δ)
    (hΔ₁ : Δ ≤ 1/(16*((k:ℝ)+1)))
    (hΔ₂ : Δ ≤ 1/(256*((k:ℝ)+2)^2))
    (hIH : ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ (M : Type)
        [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin ((m+2)+k))) M]
        [IsManifold (𝓡 ((m+2)+k)) ∞ M],
        NormalizedCornerScalarBound ((m+2)+k) (m+1) (k+1) (by omega)
          M Δ H η C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ H : ℝ, 0 ≤ H →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ A : PointedCornerModel (m+2) k δ₀ H,
        A.weightedRatio ≤ B := by
  classical
  obtain ⟨hv, hv1, δ₀, hδ₀, hann⟩ :=
    RiemannianMetric.exists_uniform_openFiber_annular_scalar_bound.{0}
      m k hm hΔ hΔ₁ hΔ₂ (by
        intro H η hH hη
        obtain ⟨C,hC,hbound⟩ := hIH H hH η hη
        exact ⟨C,hC.le,hbound⟩)
  let ε := Δ/(8*((k:ℝ)+1))
  let σ := ε^2/2048
  let v := 1-σ^2/8
  change 0 < v at hv
  change v < 1 at hv1
  obtain ⟨cminus,c,cplus,θ,hvminus,hminus,hplus,hplus1,hc,hθ,hθpi,hcθ⟩ :=
    corner_ascent_rates hv hv1
  obtain ⟨N,hmaximal⟩ := exists_maximal_rank_corner_counterexample_limit
    (m+2) k (by omega) θ hθ
  refine ⟨δ₀,hδ₀,?_⟩
  intro H hH
  obtain ⟨r₀,C,hr₀,hrhalf,hC,hannular⟩ := hann H hH
  by_contra hfail
  have hlarge : ∀ B : ℝ, ∃ A : PointedCornerModel (m+2) k δ₀ H,
      B < A.weightedRatio := by
    intro B
    by_contra h
    push Not at h
    exact hfail ⟨max 0 B,le_max_left _ _,fun A => (h A).trans (le_max_right _ _)⟩
  obtain ⟨A,T,K,hlim,hdiv,hpacking,hall,hN,hmax⟩ := hmaximal δ₀ H hlarge
  have hannularModel (A : PointedCornerModel (m+2) k δ₀ H)
      (p : openFiber A.joint A.domain A.value) :=
    hannular A.carrier A.metric A.connection A.complete A.sectional_lower
      A.f A.h A.f_smooth A.h_smooth A.domain δ₀ hδ₀.le le_rfl
      (fun x hx i => ⟨(A.unit x hx i).1,(A.unit x hx i).2,A.opposite x hx i⟩)
      A.cross A.tight A.hessian_upper A.regular A.value p A.error
      A.error_continuous A.error_nonneg A.error_sectional_lower
  obtain ⟨y,hy,φ,hφ,ref,q,b,ρ,a,hb,hρ,hascent,href,hconvref,hrefq,
      hqmin,ha,hazero,hactual,hcritical⟩ :=
    exists_corner_scalar_concentration_of_annular_bound hm hv.le hvminus hminus
      hplus hplus1 hr₀ hC
      (fun A p => by
        let := A.metric.toMetricSpace
        exact hannularModel A p)
      A T K hlim hdiv
  obtain ⟨A',T',K',hlim',hdiv',hrank⟩ :=
    exists_corner_limit_with_strictly_larger_rank (by omega) hH
      (fun j => A (φ j)) T K (hlim.comp φ hφ.tendsto_atTop)
      (hdiv.comp hφ.tendsto_atTop) y hy ref q href hconvref hrefq
      hθ hθpi hc hcθ hplus hb hρ hascent hqmin a ha hazero hactual hcritical
  exact (not_lt_of_ge (hmax A' T' K' hlim' hdiv')) hrank
