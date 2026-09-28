import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Radial












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem gradient_norm_mul_speed_ge_of_hessian_ge (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) U) {r μ : ℝ}
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = r)
    (hhess : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      μ * g.inner (γ t) v v ≤ D.hessian f (γ t) v v) :
    f (γ 1) - f (γ 0) + μ * r ^ 2 / 2 ≤
      g.tangentNorm (γ 1) (D.gradient f (γ 1)) * r := by
  have hneg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian (fun y => -f y) (γ t) v v ≤ (-μ) * g.inner (γ t) v v := by
    intro t ht v
    have heq : D.hessian (fun y => -f y) (γ t) v v = -D.hessian f (γ t) v v := by
      simpa only [neg_one_mul] using D.hessian_const_mul (-1) f (γ t) v v
    rw [heq, neg_mul]
    exact neg_le_neg (hhess t ht v)
  have hbound := D.mvfderiv_endpoint_le_of_hessian_le hU hf.neg hγ hγU hspeed hneg
  have hcs := D.abs_mvfderiv_le_gradient_norm f (γ 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)
  rw [hspeed 1 (by simp)] at hcs
  have habs := le_abs_self
    (mvfderiv (𝓡 n) f (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1))
  have hnegderiv : mvfderiv (𝓡 n) (fun y => -f y) (γ 1) =
      -mvfderiv (𝓡 n) f (γ 1) := mvfderiv_neg
  rw [hnegderiv, neg_apply] at hbound
  nlinarith



theorem gradient_norm_mul_speed_ge_of_boundary_depth_gap [T3Space M] [PreconnectedSpace M]
    (D : LeviCivitaData g)
    {U C : Set M} (hU : IsOpen U) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) U) {r κ δ η : ℝ} (hδ : 0 ≤ δ)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = r)
    (hhess : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      0 ≤ D.hessian u (γ t) v v) :
    letI := g.toMetricSpace
    let d₀ := Metric.infDist (γ 0) (frontier C)
    let d₁ := Metric.infDist (γ 1) (frontier C)
    κ * (d₀ + d₁) ≤ 1 → δ ≤ d₀ - d₁ →
    |u (γ 0) - (-d₀ + (κ / 2) * d₀ ^ 2)| ≤ η →
    |u (γ 1) - (-d₁ + (κ / 2) * d₁ ^ 2)| ≤ η →
    δ / 2 - 2 * η ≤ g.tangentNorm (γ 1) (D.gradient u (γ 1)) * r := by
  let := g.toMetricSpace
  intro d₀ d₁ hband hgap he₀ he₁
  have hbase := D.gradient_norm_mul_speed_ge_of_hessian_ge hU hu hγ hγU hspeed
    (μ := 0) (fun t ht v => by simpa using hhess t ht v)
  have hd : 0 ≤ d₀ - d₁ := hδ.trans hgap
  have hprod := mul_le_mul_of_nonneg_right hband hd
  have h₀ := (abs_le.mp he₀).2
  have h₁ := (abs_le.mp he₁).1
  nlinarith



theorem mfderiv_ne_zero_of_boundary_depth_gap [T3Space M] [PreconnectedSpace M]
    (D : LeviCivitaData g)
    {U C : Set M} (hU : IsOpen U) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) U) {r κ δ η : ℝ} (hδ : 0 ≤ δ)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = r)
    (hhess : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      0 ≤ D.hessian u (γ t) v v) :
    letI := g.toMetricSpace
    let d₀ := Metric.infDist (γ 0) (frontier C)
    let d₁ := Metric.infDist (γ 1) (frontier C)
    κ * (d₀ + d₁) ≤ 1 → δ ≤ d₀ - d₁ →
    |u (γ 0) - (-d₀ + (κ / 2) * d₀ ^ 2)| ≤ η →
    |u (γ 1) - (-d₁ + (κ / 2) * d₁ ^ 2)| ≤ η →
    4 * η < δ → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) u (γ 1) ≠ 0 := by
  let := g.toMetricSpace
  intro d₀ d₁ hband hgap he₀ he₁ hsmall
  have hb := D.gradient_norm_mul_speed_ge_of_boundary_depth_gap hU hu hγ hγU hδ
    hspeed hhess hband hgap he₀ he₁
  apply (g.tangentNorm_gradient_pos_iff u (γ 1)).mp
  change 0 < g.tangentNorm (γ 1) (D.gradient u (γ 1))
  by_contra hn
  have hzero : g.tangentNorm (γ 1) (D.gradient u (γ 1)) = 0 :=
    le_antisymm (le_of_not_gt hn) (Real.sqrt_nonneg _)
  rw [hzero, zero_mul] at hb
  linarith

end PoincareConjecture.LeviCivitaData
