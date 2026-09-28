import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Convexity.Gradient.LowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.SegmentSpeed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CompleteGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

theorem gradient_norm_ge_of_totallyConvex_gap
    (D : LeviCivitaData g) (hc : MetricComplete g) {C : Set M}
    (hconvex : ∀ (γ : ℝ → M) (a b : ℝ), g.IsGeodesicOn γ (Icc a b) →
      γ a ∈ C → γ b ∈ C → MapsTo γ (Icc a b) C)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {H A R : ℝ} (hH : 0 ≤ H) (hR : 0 < R)
    (hhess : ∀ y ∈ C, ∀ v : TangentSpace (𝓡 n) y,
      -H * g.inner y v v ≤ D.hessian f y v v)
    {p x : M} (hp : p ∈ C) (hx : x ∈ C)
    (hgap : A ≤ f x - f p) (hdist : (g.edist p x).toReal ≤ R) :
    (A - H * R ^ 2 / 2) / R ≤ g.tangentNorm x (D.gradient f x) := by
  obtain ⟨ε, hε, γ, hγ, h0, h1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p x
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hγcc : g.IsGeodesicOn γ (Icc 0 1) := fun t ht => hγ t (hI ht)
  have hγC : MapsTo γ (Icc 0 1) C := hconvex γ 0 1 hγcc (h0.symm ▸ hp) (h1.symm ▸ hx)
  have ht0 := hI (show (0 : ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨speed, hspeed⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hv := (hγ.hasDerivAt_chart_at ht0 p (by
    simpa only [h0] using mem_extChartAt_source p)).1
  have hspeed0 :
      g.tangentNorm p (deriv (fun s => extChartAt (𝓡 n) p (γ s)) 0) = speed := by
    simpa only [RiemannianMetric.chartCoefficients_self, RiemannianMetric.tangentNorm] using
      (hγ.tangentNorm_initial ht0 h0 hv).symm.trans (hspeed 0 ht0)
  have hspeedL : (speed : ℝ) = (g.edist p x).toReal := by
    have h := hγ.initial_tangentNorm_eq_of_edist_segment hε h0 hv hmin
    rw [hspeed0] at h
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ (speed : ℝ) from speed.2)] using
      congrArg ENNReal.toReal h
  have hb := D.gradient_norm_mul_speed_ge_of_hessian_ge isOpen_univ hf.contMDiffOn
    hγcc (fun _ _ => mem_univ _) (μ := -H)
    (fun t ht => (hspeed t (hI ht)).trans hspeedL)
    (fun t ht v => hhess (γ t) (hγC ht) v)
  rw [h0, h1] at hb
  have hsq : (g.edist p x).toReal ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ ENNReal.toReal_nonneg hR.le).mpr hdist
  have herror := mul_le_mul_of_nonneg_left hsq hH
  have hnorm := Real.sqrt_nonneg (g.inner x (D.gradient f x) (D.gradient f x))
  have hlength := mul_le_mul_of_nonneg_left hdist hnorm
  apply (div_le_iff₀ hR).mpr
  change 0 ≤ g.tangentNorm x (D.gradient f x) at hnorm
  change g.tangentNorm x (D.gradient f x) * (g.edist p x).toReal ≤
    g.tangentNorm x (D.gradient f x) * R at hlength
  nlinarith

theorem exists_uniform_gradient_bound_of_compact_totallyConvex
    (D : LeviCivitaData g) (hc : MetricComplete g) {C : Set M}
    (hC : IsCompact C)
    (hconvex : ∀ (γ : ℝ → M) (a b : ℝ), g.IsGeodesicOn γ (Icc a b) →
      γ a ∈ C → γ b ∈ C → MapsTo γ (Icc a b) C)
    {p : M} (hp : p ∈ C) {A : ℝ} (hA : 0 < A) :
    ∃ R : ℝ, 0 < R ∧ (∀ x ∈ C, (g.edist p x).toReal ≤ R) ∧
      ∀ (f : M → ℝ), ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f →
      ∀ H : ℝ, 0 ≤ H → H * R ^ 2 ≤ A →
      (∀ y ∈ C, ∀ v : TangentSpace (𝓡 n) y,
        -H * g.inner y v v ≤ D.hessian f y v v) →
      ∀ x ∈ C, A ≤ f x - f p → A / (2 * R) ≤ g.tangentNorm x (D.gradient f x) := by
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn ⟨p, hp⟩ (g.continuous_toReal_edist p).continuousOn
  let R := max 1 (g.edist p q).toReal
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdist (x : M) (hx : x ∈ C) : (g.edist p x).toReal ≤ R :=
    (hmax hx).trans (le_max_right _ _)
  refine ⟨R, hR, hdist, ?_⟩
  intro f hf H hH herror hhess x hx hgap
  have h := D.gradient_norm_ge_of_totallyConvex_gap hc hconvex hf hH hR
    hhess hp hx hgap (hdist x hx)
  apply le_trans ?_ h
  have he : A / (2 * R) = (A / 2) / R := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hR.le
  linarith

end PoincareConjecture.LeviCivitaData
