import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.TotalExponential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.NoBranching
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity.Derivative








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T3Space M] in
private theorem quadratic_upper_bound_on_geodesic
    (D : LeviCivitaData g) {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc (0 : ℝ) 1))
    {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    {R H : ℝ}
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = R)
    (hhess : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian f (γ t) v v ≤ H * g.inner (γ t) v v) :
    f (γ 1) ≤ f (γ 0) + deriv (f ∘ γ) 0 + H * R ^ 2 / 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let F := f ∘ γ
  let V := fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1
  let A := fun t => D.hessian f (γ t) (V t) (V t)
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt F (deriv F t) t := by
    apply DifferentiableAt.hasDerivAt
    apply (contMDiffAt_iff_contDiffAt.mp
      (((hf.contMDiffAt (hU.mem_nhds (hγU t ht))).of_le
        (show (1 : ℕ∞ω) ≤ ∞ by simp)).comp t (hγ.contMDiffAt ht))).differentiableAt
      (by simp)
  have hsecond (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (deriv F) (A t) t :=
    D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn hU hf hγ
      ⟨ht.1.le, ht.2.le⟩ (hγU t ⟨ht.1.le, ht.2.le⟩)
  have hA (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : A t ≤ H * R ^ 2 := by
    have hnorm := hspeed t ⟨ht.1.le, ht.2.le⟩
    have hinner : g.inner (γ t) (V t) (V t) = R ^ 2 := by
      change inner ℝ (V t) (V t) = R ^ 2
      rw [real_inner_self_eq_norm_sq]
      exact congrArg (fun a : ℝ => a ^ 2) hnorm
    simpa only [hinner] using hhess t ⟨ht.1.le, ht.2.le⟩ (V t)
  simpa only [F, Function.comp_apply, one_mul, one_pow, mul_one] using
    Poincare.Analysis.quadratic_upper_bound_of_hasDerivAt2_le
      (by norm_num : (0 : ℝ) ≤ 1) hfirst hsecond hA




theorem gradient_norm_le_of_lower_oscillation_hessian
    (D : LeviCivitaData g) (hc : MetricComplete g) (x : M)
    {R ε H : ℝ} (hR : 0 < R) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    {U : Set M} (hU : IsOpen U)
    (hball : ∀ y, g.edist x y ≤ ENNReal.ofReal R → y ∈ U)
    {f : M → ℝ} (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hlower : ∀ y, g.edist x y ≤ ENNReal.ofReal R → f x - ε ≤ f y)
    (hhess : ∀ y, g.edist x y ≤ ENNReal.ofReal R →
      ∀ v : TangentSpace (𝓡 n) y, D.hessian f y v v ≤ H * g.inner y v v) :
    g.tangentNorm x (D.gradient f x) ≤ ε / R + H * R / 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := g.tangentNorm x (D.gradient f x)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hA with hzero | hpos
  · change A ≤ _
    rw [← hzero]
    positivity
  let v : TangentSpace (𝓡 n) x := (-R / A) • D.gradient f x
  have hv : g.tangentNorm x v = R := by
    change ‖(-R / A) • D.gradient f x‖ = R
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hR.le) hA)]
    change -(-R / A) * A = R
    field_simp
  let γ := g.globalGeodesic hc x v
  obtain ⟨hgeo, hx, hvel⟩ := g.globalGeodesic_spec hc x v
  change γ 0 = x at hx
  have hγ : g.IsGeodesicOn γ (Icc (0 : ℝ) 1) := fun t _ => hgeo t (mem_univ _)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = R := by
    exact (Poincare.VolumeComparison.tangentNorm_eq_of_mem_Icc g hγ ht h0).trans
      ((Poincare.VolumeComparison.tangentNorm_coordDeriv_eq g hγ h0 hx hvel).symm.trans hv)
  have hdist (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g.edist x (γ t) ≤ ENNReal.ofReal R := by
    have hh := Poincare.VolumeComparison.edist_le_of_geodesic_speed_Icc g hγ hspeed h0 ht
    rw [hx, zero_sub, abs_neg, abs_of_nonneg ht.1] at hh
    exact hh.trans (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left hR.le ht.2))
  have hγU := fun t ht => hball (γ t) (hdist t ht)
  have htaylor := quadratic_upper_bound_on_geodesic D hγ hU hf hγU hspeed
    (fun t ht => hhess (γ t) (hdist t ht))
  have hd : deriv (f ∘ γ) 0 = -R * A := by
    have hchain := congrArg (fun L => L (1 : ℝ))
      (mfderiv_comp 0
        ((hf.contMDiffAt (hU.mem_nhds (hγU 0 h0))).mdifferentiableAt (by simp))
        ((hγ.contMDiffAt h0).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at hchain
    change deriv (f ∘ γ) 0 = mvfderiv (𝓡 n) f (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) at hchain
    rw [g.mfderiv_globalGeodesic_zero hc x v, hx, ← D.inner_gradient] at hchain
    rw [hchain]
    dsimp only [v]
    rw [map_smul, smul_eq_mul]
    have hinner : g.inner x (D.gradient f x) (D.gradient f x) = A ^ 2 := by
      change inner ℝ (D.gradient f x) (D.gradient f x) = A ^ 2
      exact real_inner_self_eq_norm_sq _
    rw [hinner]
    field_simp
  rw [hx, hd] at htaylor
  have hlow := hlower (γ 1) (hdist 1 h1)
  change A ≤ _
  apply (mul_le_mul_iff_right₀ hR).mp
  have hrewrite : R * (ε / R + H * R / 2) = ε + H * R ^ 2 / 2 := by
    field_simp
  rw [hrewrite]
  nlinarith

end PoincareConjecture.LeviCivitaData
