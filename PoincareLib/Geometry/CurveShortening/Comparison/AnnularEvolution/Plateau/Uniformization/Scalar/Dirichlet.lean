import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.Energy
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.WeakDirichlet
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Scalar Dirichlet potentials for annular uniformization

The retained-metric Poincare inequality and Lax--Milgram construct the
zero-boundary correction to a prescribed smooth boundary extension. This is
the scalar Dirichlet step, before harmonic conjugates or global coordinates.
Source: Morrey, ICM 1950, printed pp. 184-187, Dirichlet minimization and weak
equations; M07's retained-metric Dirichlet construction.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareMT.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- A bounded planar domain inherits a genuine retained-metric Poincare inequality from a
containing ball. Source: M07 harmonic-coordinate energy. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem exists_testPoincare_of_subset_ball {Ω : Set Plane} {R : ℝ}
    (hR : 0 < R) (hΩ : Ω ⊆ Metric.ball 0 R) :
    ∃ P : ℝ, 0 ≤ P ∧ HasTestPoincare D Ω P := by
  obtain ⟨P, hP0, hP⟩ := HarmonicCoordinates.exists_metric_poincare_on_ball g D hR
  refine ⟨P, hP0, fun f => ?_⟩
  let f' : EnergyTest D (Metric.ball 0 R) :=
    ⟨f.1, f.smooth, f.hasCompactSupport, f.support_subset.trans hΩ⟩
  have h := hP f'
  rw [← real_inner_self_eq_norm_sq, testToL2_inner] at h ⊢
  exact h

/-- The actual scalar Laplacian of a smooth compact boundary extension in L2.
Source: Morrey, printed pp. 184-187, scalar Dirichlet forcing. -/
def boundaryLaplacianL2 (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q) :
    Lp ℝ 2 g.volumeMeasure :=
  ((D.continuous_laplacian hq).memLp_of_hasCompactSupport
    (D.hasCompactSupport_laplacian hqc)).toLp (D.laplacian q)

/-- The forcing functional for the harmonic correction to `q`. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def boundaryForcing (Ω : Set Plane) (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q) :
    H1Zero D Ω →L[ℝ] ℝ :=
  (innerSL ℝ (boundaryLaplacianL2 D q hq hqc)).comp (toL2 D Ω)

/-- The L2 forcing is the classical retained-volume Laplacian pairing. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem boundaryForcing_coe (Ω : Set Plane) (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q)
    (f : EnergyTest D Ω) :
    boundaryForcing D Ω q hq hqc (f : H1Zero D Ω) =
      ∫ x, f x * D.laplacian q x ∂g.volumeMeasure := by
  change ⟪boundaryLaplacianL2 D q hq hqc, toL2 D Ω f⟫_ℝ = _
  rw [toL2_coe, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((D.continuous_laplacian hq).memLp_of_hasCompactSupport
    (D.hasCompactSupport_laplacian hqc)).coeFn_toLp, f.memLp.coeFn_toLp]
      with x hx hfx
  change inner ℝ ((boundaryLaplacianL2 D q hq hqc) x) ((testToL2 D Ω f) x) = _
  rw [show (boundaryLaplacianL2 D q hq hqc) x = D.laplacian q x from hx,
    show (testToL2 D Ω f) x = f x from hfx]
  simp

/-- Green's identity fixes the sign of the harmonic-correction forcing. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem boundaryForcing_eq_neg_gradient (Ω : Set Plane) (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q)
    (f : EnergyTest D Ω) :
    boundaryForcing D Ω q hq hqc (f : H1Zero D Ω) =
      -(∫ x, g.inner x (D.gradient f x) (D.gradient q x) ∂g.volumeMeasure) := by
  rw [boundaryForcing_coe]
  exact D.integral_mul_laplacian f.smooth hq f.hasCompactSupport

/-- An actual unique weak harmonic correction on every bounded planar domain.
The correction belongs to the zero-boundary space, so the potential has the
prescribed Sobolev trace of `q`. Source: Morrey, printed pp. 184-187. -/
theorem existsUnique_harmonic_correction {Ω : Set Plane} {R : ℝ}
    (hR : 0 < R) (hΩ : Ω ⊆ Metric.ball 0 R) (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q) :
    ∃! w : H1Zero D Ω, ∀ f : EnergyTest D Ω,
      gradientEnergy D Ω w (f : H1Zero D Ω) +
        (∫ x, g.inner x (D.gradient f x) (D.gradient q x) ∂g.volumeMeasure) = 0 := by
  obtain ⟨P, hP0, hP⟩ := exists_testPoincare_of_subset_ball D hR hΩ
  let ell := boundaryForcing D Ω q hq hqc
  let w := weakDirichlet D Ω hP0 hP ell
  refine ⟨w, ?_, ?_⟩
  · intro f
    rw [show gradientEnergy D Ω w f = ell f from weakDirichlet_spec hP0 hP ell f]
    change boundaryForcing D Ω q hq hqc f + _ = 0
    rw [boundaryForcing_eq_neg_gradient, neg_add_cancel]
  · intro v hv
    apply weakDirichlet_unique_of_test hP0 hP ell v
    intro f
    change gradientEnergy D Ω v f = boundaryForcing D Ω q hq hqc f
    rw [boundaryForcing_eq_neg_gradient]
    exact eq_neg_of_add_eq_zero_left (hv f)

/-- The affine Dirichlet functional with its fixed constant term omitted. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def affineDirichletEnergy (Ω : Set Plane) (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q)
    (v : H1Zero D Ω) : ℝ :=
  gradientEnergy D Ω v v - 2 * boundaryForcing D Ω q hq hqc v

/-- The constructed correction attains the affine Dirichlet minimum, with the exact
nonnegative energy difference for every zero-boundary variation. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem exists_harmonic_correction_minimum {Ω : Set Plane} {R : ℝ}
    (hR : 0 < R) (hΩ : Ω ⊆ Metric.ball 0 R) (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q) :
    ∃ w : H1Zero D Ω,
      (∀ f : EnergyTest D Ω, gradientEnergy D Ω w f +
        (∫ x, g.inner x (D.gradient f x) (D.gradient q x) ∂g.volumeMeasure) = 0) ∧
      (∀ v : H1Zero D Ω,
        affineDirichletEnergy D Ω q hq hqc (w + v) -
          affineDirichletEnergy D Ω q hq hqc w = gradientEnergy D Ω v v) ∧
      ∀ v : H1Zero D Ω,
        affineDirichletEnergy D Ω q hq hqc w ≤ affineDirichletEnergy D Ω q hq hqc v := by
  obtain ⟨P, hP0, hP⟩ := exists_testPoincare_of_subset_ball D hR hΩ
  let ell := boundaryForcing D Ω q hq hqc
  let w := weakDirichlet D Ω hP0 hP ell
  have heq (v : H1Zero D Ω) : gradientEnergy D Ω w v = ell v :=
    weakDirichlet_spec hP0 hP ell v
  have hdiff (v : H1Zero D Ω) :
      affineDirichletEnergy D Ω q hq hqc (w + v) -
        affineDirichletEnergy D Ω q hq hqc w = gradientEnergy D Ω v v := by
    simp only [affineDirichletEnergy, map_add, add_apply]
    rw [gradientEnergy_symm v w]
    simp only [heq]
    change _ - 2 * (ell w + ell v) - (_ - 2 * ell w) = _
    ring
  refine ⟨w, ?_, hdiff, ?_⟩
  · intro f
    rw [heq]
    change boundaryForcing D Ω q hq hqc f + _ = 0
    rw [boundaryForcing_eq_neg_gradient, neg_add_cancel]
  · intro v
    have h := hdiff (v - w)
    rw [add_sub_cancel] at h
    exact sub_nonneg.mp (h.symm ▸ gradientEnergy_self_nonneg (v - w))

/-- The fixed doubly-connected planar domain used for the scalar potential. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def scalarAnnulus : Set Plane := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}

private def outerBoundaryBump : ContDiffBump (0 : Plane) :=
  ⟨2, 3, by norm_num, by norm_num⟩

private def innerBoundaryBump : ContDiffBump (0 : Plane) :=
  ⟨1, 3 / 2, by norm_num, by norm_num⟩

/-- A genuine smooth compact extension of the annular boundary values 0 and 1. It is built
from radial bumps, independently of the metric or the solution. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def annularBoundaryExtension (x : Plane) : ℝ :=
  outerBoundaryBump x - innerBoundaryBump x

/-- The actual difference of radial bumps gives a globally smooth annular boundary
extension. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project
construction in `proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`;
scalar boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem annularBoundaryExtension_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ annularBoundaryExtension := by
  apply contMDiff_iff_contDiff.mpr
  exact outerBoundaryBump.contDiff.sub innerBoundaryBump.contDiff

/-- The actual annular boundary extension has compact support. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem annularBoundaryExtension_compact : HasCompactSupport annularBoundaryExtension :=
  outerBoundaryBump.hasCompactSupport.sub innerBoundaryBump.hasCompactSupport

/-- The fixed smooth extension has literal value zero on the inner unit circle. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem annularBoundaryExtension_inner {x : Plane} (hx : ‖x‖ = 1) :
    annularBoundaryExtension x = 0 := by
  have ho : outerBoundaryBump x = 1 := outerBoundaryBump.one_of_mem_closedBall (by
    simp [outerBoundaryBump, hx])
  have hi : innerBoundaryBump x = 1 := innerBoundaryBump.one_of_mem_closedBall (by
    simp [innerBoundaryBump, hx])
  simp [annularBoundaryExtension, ho, hi]

/-- The fixed smooth extension has literal value one on the circle of radius two. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem annularBoundaryExtension_outer {x : Plane} (hx : ‖x‖ = 2) :
    annularBoundaryExtension x = 1 := by
  have ho : outerBoundaryBump x = 1 := outerBoundaryBump.one_of_mem_closedBall (by
    simp [outerBoundaryBump, hx])
  have hi : innerBoundaryBump x = 0 := innerBoundaryBump.zero_of_le_dist (by
    norm_num [innerBoundaryBump, hx])
  simp [annularBoundaryExtension, ho, hi]

/-- Every smooth positive planar metric has an actual weak scalar potential
with the annular boundary values 0 and 1 in the H1 trace sense. Its correction
minimizes the affine Dirichlet functional. No conformal map is assumed.
Source: Morrey, printed pp. 184-187, scalar Dirichlet minimization. -/
theorem exists_annular_harmonic_potential :
    ∃ w : H1Zero D scalarAnnulus,
      (∀ f : EnergyTest D scalarAnnulus,
        gradientEnergy D scalarAnnulus w f +
          (∫ x, g.inner x (D.gradient f x) (D.gradient annularBoundaryExtension x)
            ∂g.volumeMeasure) = 0) ∧
      ∀ v : H1Zero D scalarAnnulus,
        affineDirichletEnergy D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w ≤
        affineDirichletEnergy D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact v := by
  have hΩ : scalarAnnulus ⊆ Metric.ball (0 : Plane) 2 := by
    intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using hx.2
  obtain ⟨w, hw, -, hmin⟩ := exists_harmonic_correction_minimum D
    (by norm_num : (0 : ℝ) < 2) hΩ annularBoundaryExtension
      annularBoundaryExtension_smooth annularBoundaryExtension_compact
  exact ⟨w, hw, hmin⟩

end PoincareMT.M64Uniformization
