import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.AreaMass
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.AreaDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.AreaBound

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

theorem regularLevelArea_le_of_gradient_hessian_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {g : RiemannianMetric (n + 1) M}
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (n + 1)) x),
      -1 ≤ D.sectionalCurvature x v w)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I) (hproper : IsProperMap (I.restrictPreimage f))
    {l L H a d b R : ℝ} (hl : 0 < l) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (had : a < d) (hdb : d ≤ b) (hslab : Icc a b ⊆ I)
    (hR : 0 < R) (p : M)
    (hspeed : ∀ x : M, f x ∈ I →
      l ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ L)
    (hhess : ∀ x : M, f x ∈ I → ∀ v : TangentSpace (𝓡 (n + 1)) x,
      D.hessian f x v v ≤ H * g.inner x v v)
    (hball : f ⁻¹' Icc a b ⊆ g.ball p R) :
    ∀ t ∈ Icc d b, g.regularLevelArea hf t ≤
      L * RiemannianMetric.modelVolume (n + 1) 1 R / (d - a) *
        Real.exp (((n : ℝ) * H / l ^ 2) * (b - a)) := by
  have hreg (x : M) (hx : f x ∈ I) :
      mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    (g.tangentNorm_gradient_pos_iff f x).mp (hl.trans_le (hspeed x hx).1)
  have hcont := (D.first_variation_regularLevelArea hf hI hproper hreg).1.continuousOn
  have hd (t : ℝ) (ht : t ∈ I) := D.hasDerivAt_regularLevelArea_and_le_of_hessian_le
    hf hI hproper hl hH (fun x hx => (hspeed x hx).1) hhess ht
  have hmass := g.integral_regularLevelArea_le_modelVolume hf D hc hsec
    hproper hreg (had.le.trans hdb) hslab hL hR p
    (fun x hx => (hspeed x (hslab hx)).2) hball
  have h := Poincare.ODE.le_mul_exp_of_integral_le_of_deriv_le_mul had hdb
    (hcont.mono hslab) (fun t _ => g.regularLevelArea_nonneg hf t)
    (fun t ht => (hd t (hslab (Ioo_subset_Icc_self ht))).1)
    (fun t ht => (hd t (hslab (Ioo_subset_Icc_self ht))).2) hmass
  have hK : 0 ≤ (n : ℝ) * H / l ^ 2 := by positivity
  simpa only [max_eq_left hK] using h

end PoincareConjecture.LeviCivitaData
