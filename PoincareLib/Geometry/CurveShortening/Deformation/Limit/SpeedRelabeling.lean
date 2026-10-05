import PoincareLib.Geometry.CurveShortening.Deformation.Analysis.Arclength.PeriodicArclength
import PoincareLib.Geometry.CurveShortening.Deformation.Limit.SpeedBounds
import PoincareLib.Geometry.RicciFlow.CurveShortening.Integral.Periodicity

/-!
# Fixed constant-speed relabeling of the actual solution

Morgan--Tian Claim 19.28, printed pp. 459-460. At a strict interior
reference time the actual positive speed is smooth and periodic. Its
arc-length inverse supplies one smooth relabeling, fixed for all times.
-/

set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

/-- The speed of the genuine fixed pullback is multiplied by the
positive relabeling derivative; Claim 19.28, printed pp. 459-460. -/
theorem m65CurveSpeed_fixed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {phi : ℝ → ℝ} {x d t : ℝ}
    (hphi : HasDerivAt phi d x) (hd : 0 < d) (ht : t ∈ Icc a b) :
    curveSpeed F (fun y r => c (phi y) r) t x = d * curveSpeed F c t (phi x) := by
  have hchain := mfderiv_comp_apply (f := phi) (g := fun y => c y t) x
    ((hc.spatial_regular t ht (phi x)).mdifferentiableAt (by norm_num))
    hphi.differentiableAt.mdifferentiableAt (1 : ℝ)
  have hparam : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) phi x (1 : ℝ) = d := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hphi.deriv
  have hvelocity : curveVelocity (n := n) (fun y => c (phi y) t) x =
      d • curveVelocity (n := n) (fun y => c y t) (phi x) := by
    change curveVelocity (n := n) (fun y => c (phi y) t) x = _ at hchain
    erw [hparam] at hchain
    rw [hchain]
    let L : ℝ →L[ℝ] TangentSpace (𝓡 n) (c (phi x) t) :=
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t) (phi x)
    change L d = d • L 1
    simpa only [smul_eq_mul, mul_one] using L.map_smul d (1 : ℝ)
  let g := F.metric t
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change ‖curveVelocity (n := n) (fun y => c (phi y) t) x‖ =
    d * ‖curveVelocity (n := n) (fun y => c y t) (phi x)‖
  rw [hvelocity, norm_smul, Real.norm_eq_abs, abs_of_pos hd]

/-- At every strict interior time the actual solution has a fixed
smooth degree-one relabeling with constant initial speed; Claim 19.28,
printed pp. 459-460. -/
theorem m65ShrinkingCurve_exists_constantSpeed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {s : ℝ} (hs : s ∈ Ioo a b) :
    ∃ phi : ℝ ≃o ℝ, phi 0 = 0 ∧
      (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
      ContDiff ℝ ∞ (phi : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (phi : ℝ → ℝ) x) ∧
      ∀ x, curveSpeed F (fun y t => c (phi y) t) s x = m62Length F c s / curvePeriod := by
  have hv : ContDiff ℝ ∞ (curveSpeed F c s) :=
    (M62.speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, hs⟩)
  obtain ⟨phi, hzero, hperiod, hsmooth, hderiv, hpos, hconstant⟩ :=
    M65.exists_periodic_arclength_reparam hv
      (M62.speed_pos F c hc (Ioo_subset_Icc_self hs))
      (show 0 < curvePeriod by unfold curvePeriod; positivity)
      (M62.speed_periodic F c hc (Ioo_subset_Icc_self hs))
  refine ⟨phi, hzero, hperiod, hsmooth, hpos, ?_⟩
  intro x
  rw [m65CurveSpeed_fixed_relabeling c hc
    ((hsmooth.differentiable (by simp) x).hasDerivAt) (hpos x) (Ioo_subset_Icc_self hs)]
  exact hconstant x

/-- A fixed increasing relabeling retains both actual speed comparison
bounds, allowing the initial constant speed to be used uniformly on the
whole good cell; Claim 19.28, printed p. 460. -/
theorem m65RelabeledSpeed_exp_bounds_on (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 H : ℝ}
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {I : Set ℝ} (hI : Convex ℝ I) (hsub : I ⊆ Ioo a b)
    (hcurv : ∀ t ∈ I, ∀ x, m62CurvatureSquared F c t x ≤ H)
    {phi : ℝ → ℝ} (hphi : Differentiable ℝ phi)
    (hpos : ∀ x, 0 < deriv phi x) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (x : ℝ) :
    Real.exp (-(K2 + H) * |t - s|) *
        curveSpeed F (fun y r => c (phi y) r) s x ≤
      curveSpeed F (fun y r => c (phi y) r) t x ∧
      curveSpeed F (fun y r => c (phi y) r) t x ≤
        Real.exp ((K2 + H) * |t - s|) *
          curveSpeed F (fun y r => c (phi y) r) s x := by
  rw [m65CurveSpeed_fixed_relabeling c hc (hphi x).hasDerivAt (hpos x)
    (Ioo_subset_Icc_self (hsub hs)),
    m65CurveSpeed_fixed_relabeling c hc (hphi x).hasDerivAt (hpos x)
      (Ioo_subset_Icc_self (hsub ht))]
  have hbound := m65Speed_exp_bounds_on c hc bounds hI hsub hcurv hs ht (phi x)
  constructor
  · simpa only [mul_left_comm (deriv phi x)] using
      mul_le_mul_of_nonneg_left hbound.1 (hpos x).le
  · simpa only [mul_left_comm (deriv phi x)] using
      mul_le_mul_of_nonneg_left hbound.2 (hpos x).le

end PoincareMT
