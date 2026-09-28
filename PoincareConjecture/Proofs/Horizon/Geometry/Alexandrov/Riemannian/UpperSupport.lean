import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.ComparisonODE
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.RadialHessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Tail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Alexandrov

private theorem second_deriv_cosh {r : ℝ → ℝ} {t : ℝ}
    (hr : ContDiffAt ℝ 2 r t) :
    deriv (deriv (fun s => Real.cosh (r s))) t =
      Real.cosh (r t) * deriv r t ^ 2 +
        Real.sinh (r t) * deriv (deriv r) t := by
  have hfirst : deriv (fun s => Real.cosh (r s)) =ᶠ[𝓝 t]
      (fun s => Real.sinh (r s) * deriv r s) := by
    filter_upwards [hr.eventually (by norm_num)] with s hs
    exact (hs.differentiableAt (by norm_num)).hasDerivAt.cosh.deriv
  have hrd : DifferentiableAt ℝ (deriv r) t :=
    (hr.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (((hr.differentiableAt (by norm_num)).hasDerivAt.sinh).mul
    hrd.hasDerivAt).deriv
  change deriv (fun s => Real.sinh (r s) * deriv r s) t =
    Real.cosh (r t) * deriv r t * deriv r t + Real.sinh (r t) * deriv (deriv r) t at hd
  rw [hfirst.deriv_eq, hd]
  ring



theorem second_deriv_shifted_cosh_le {r : ℝ → ℝ} {t l C : ℝ}
    (hr : ContDiffAt ℝ 2 r t) (hrpos : 0 < r t) (hl : 0 ≤ l)
    (hbound : deriv (deriv r) t ≤
      (Real.cosh (r t) / Real.sinh (r t)) * (C - deriv r t ^ 2)) :
    deriv (deriv (fun s => Real.cosh (l + r s))) t ≤
      (Real.sinh (l + r t) * Real.cosh (r t) / Real.sinh (r t)) * C := by
  have hsinh : 0 < Real.sinh (r t) := Real.sinh_pos_iff.mpr hrpos
  have hshift := second_deriv_cosh ((contDiffAt_const (c := l)).add hr)
  simp only [deriv_const_add'] at hshift
  rw [hshift]
  have hsinhshift : 0 ≤ Real.sinh (l + r t) :=
    Real.sinh_nonneg_iff.mpr (add_nonneg hl hrpos.le)
  have hmul := mul_le_mul_of_nonneg_left hbound hsinhshift
  have hcoeff : Real.cosh (l + r t) ≤
      Real.sinh (l + r t) * Real.cosh (r t) / Real.sinh (r t) := by
    apply (le_div_iff₀ hsinh).mpr
    rw [Real.cosh_add, Real.sinh_add]
    have hid := Real.cosh_sq_sub_sinh_sq (r t)
    have hl' : 0 ≤ Real.sinh l := Real.sinh_nonneg_iff.mpr hl
    nlinarith
  have hcoeffmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (deriv r t))
  calc
    _ ≤ (Real.sinh (l + r t) * Real.cosh (r t) / Real.sinh (r t)) * deriv r t ^ 2 +
        Real.sinh (l + r t) *
          ((Real.cosh (r t) / Real.sinh (r t)) * (C - deriv r t ^ 2)) :=
      add_le_add hcoeffmul hmul
    _ = _ := by ring



theorem exists_small_hyperbolic_support_shift {d C ε : ℝ}
    (hd : 0 < d) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      (Real.sinh d * Real.cosh ((1 - δ) * d) / Real.sinh ((1 - δ) * d)) * C ≤
        Real.cosh d * C + ε := by
  let A : ℝ → ℝ := fun δ =>
    (Real.sinh d * Real.cosh ((1 - δ) * d) / Real.sinh ((1 - δ) * d)) * C
  have hsinh : Real.sinh d ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hd)
  have hcont : ContinuousAt A 0 := by
    apply ContinuousAt.mul_const
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa only [sub_zero, one_mul] using hsinh
  have hzero : A 0 = Real.cosh d * C := by
    dsimp [A]
    simp only [sub_zero, one_mul]
    field_simp
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), A δ < Real.cosh d * C + ε :=
    hcont.eventually_lt continuousAt_const (by rw [hzero]; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let δ := min (r / 2) (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, (min_le_right _ _).trans (by norm_num), ?_⟩
  exact (hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδr)).le

end Poincare.Alexandrov

namespace PoincareConjecture.RiemannianMetric.Alexandrov

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_cosh_distance_upper_support_of_shift
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (u v : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x u v)
    (p : M) {γ : ℝ → M} {I : Set ℝ} {t δ : ℝ}
    (hγ : g.IsGeodesicOn γ I) (ht : t ∈ I) (hpx : p ≠ γ t)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ u : ℝ → ℝ, ContDiffAt ℝ 2 u t ∧
      u t = Real.cosh (g.edist p (γ t)).toReal ∧
      (∀ᶠ s in 𝓝 t, Real.cosh (g.edist p (γ s)).toReal ≤ u s) ∧
      deriv (deriv u) t ≤
        (Real.sinh (g.edist p (γ t)).toReal *
          Real.cosh ((1 - δ) * (g.edist p (γ t)).toReal) /
            Real.sinh ((1 - δ) * (g.edist p (γ t)).toReal)) *
          g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
  obtain ⟨ε, η, R, L, e, v, B, hε, hη, hη0, hη1, hηmin, hR, hdR,
      hL, hnorm, he, he0, hed, hradial, hv, hv0, hx, hvnorm, hsplit,
      hleft, hmin, hi, hvB, hBU, heB, hB, hBi, hzero, hnormB, hmajor⟩ :=
    g.exists_smooth_radial_inverse_branch_of_shift D hcomplete p (γ t) hpx hδ hδhalf
  let d := (g.edist p (γ t)).toReal
  have hd : 0 < d := by
    have := norm_pos_iff.mpr hv0
    rw [hvnorm] at this
    dsimp [d]
    nlinarith [ENNReal.toReal_nonneg (a := g.edist p (γ t))]
  have hxB : B v = γ t := (heB hvB).symm.trans hx
  have htB : γ t ∈ B.target := hxB ▸ B.map_source hvB
  have hγt := Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ ht
  have hrt : ‖B.symm (γ t)‖ = ‖v‖ := by rw [← hxB, B.left_inv hvB]
  have hnormt : ‖B.symm (γ t)‖ = (1 - δ) * d := hrt.trans hvnorm
  have hr : ContDiffAt ℝ 2 (fun s => ‖B.symm (γ s)‖) t := by
    have h := (hnormB.contMDiffAt (B.open_target.mem_nhds htB)).comp t hγt
    exact (contMDiffAt_iff_contDiffAt.mp h).of_le (by norm_cast)
  let u : ℝ → ℝ := fun s => Real.cosh (δ * d + ‖B.symm (γ s)‖)
  have hu : ContDiffAt ℝ 2 u t := by
    exact (contDiffAt_const.add hr).cosh
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · dsimp [u]
    rw [hnormt, show δ * d + (1 - δ) * d = d by ring]
  · filter_upwards [hγt.continuousAt.preimage_mem_nhds
      (B.open_target.mem_nhds htB)] with s hs
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (add_nonneg (mul_nonneg hδ.le hd.le) (norm_nonneg _))]
    exact hmajor (γ s) hs
  · have hi1 : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
      have h := hi 1 (by simp)
      rw [one_smul] at h
      exact h
    have hbound := deriv2_inverse_radius_le_hyperbolic g D hsec he hnorm
      (fun w hw => (hradial w hw).1) B heB hBi hv hvB hv0 hi1 hmin hγ ht hx
    have h := Poincare.Alexandrov.second_deriv_shifted_cosh_le hr
      (by rw [hrt]; exact norm_pos_iff.mpr hv0) (mul_nonneg hδ.le hd.le)
      (by rw [hrt]; exact hbound)
    rw [hnormt, show δ * d + (1 - δ) * d = d by ring] at h
    exact h




theorem exists_cosh_distance_upper_support
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (u v : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x u v)
    (p : M) {γ : ℝ → M} {I : Set ℝ} {t : ℝ}
    (hγ : g.IsGeodesicOn γ I) (ht : t ∈ I) (hpx : p ≠ γ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → ℝ, ContDiffAt ℝ 2 u t ∧
      u t = Real.cosh (g.edist p (γ t)).toReal ∧
      (∀ᶠ s in 𝓝 t, Real.cosh (g.edist p (γ s)).toReal ≤ u s) ∧
      deriv (deriv u) t ≤ Real.cosh (g.edist p (γ t)).toReal *
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) + ε := by
  have hd : 0 < (g.edist p (γ t)).toReal := by
    let := g.toMetricSpace
    exact dist_pos.mpr hpx
  obtain ⟨δ, hδ, hδhalf, hcoef⟩ :=
    Poincare.Alexandrov.exists_small_hyperbolic_support_shift
      (C := g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) hd hε
  obtain ⟨u, hu, htouch, hmajor, hbound⟩ :=
    exists_cosh_distance_upper_support_of_shift g D hcomplete hsec p hγ ht hpx hδ hδhalf
  exact ⟨u, hu, htouch, hmajor, hbound.trans hcoef⟩

end PoincareConjecture.RiemannianMetric.Alexandrov
