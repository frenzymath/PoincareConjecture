import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.Dirichlet

/-!
# The actual distributional annular harmonic potential

The variational correction is added to the prescribed boundary extension in
the retained-volume L2 space. Density and Green's identity prove the scalar
harmonic equation against every compact smooth annular test.
Source: Morrey, ICM 1950, printed pp. 184-187, weak harmonic representatives.

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

/-- The scalar potential as an actual retained-volume L2 class, rather than its
zero-boundary correction alone. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with
the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def scalarPotentialL2 (Ω : Set Plane) (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q)
    (w : H1Zero D Ω) : Lp ℝ 2 g.volumeMeasure :=
  (hq.continuous.memLp_of_hasCompactSupport hqc).toLp q + toL2 D Ω w

/-- Pairing the actual L2 Laplacian with an L2 map equals the scalar integral. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem boundaryLaplacian_inner (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q)
    (U : Lp ℝ 2 g.volumeMeasure) :
    ⟪boundaryLaplacianL2 D q hq hqc, U⟫_ℝ =
      ∫ x, U x * D.laplacian q x ∂g.volumeMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((D.continuous_laplacian hq).memLp_of_hasCompactSupport
    (D.hasCompactSupport_laplacian hqc)).coeFn_toLp] with x hx
  change inner ℝ ((boundaryLaplacianL2 D q hq hqc) x) (U x) = _
  rw [show (boundaryLaplacianL2 D q hq hqc) x = D.laplacian q x from hx]
  simp

/-- Green's formula extends to every zero-boundary H1 correction by density. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem boundaryForcing_test_source {Ω : Set Plane} (f : EnergyTest D Ω)
    (w : H1Zero D Ω) :
    boundaryForcing D Ω f f.smooth f.hasCompactSupport w =
      -gradientEnergy D Ω w (f : H1Zero D Ω) := by
  induction w using Completion.induction_on with
  | hp =>
    apply isClosed_eq
    · fun_prop
    · fun_prop
  | ih v =>
    rw [boundaryForcing_eq_neg_gradient, gradientEnergy_coe]

/-- The scalar Laplacian pairing of the total potential is exactly the variational residual.
This identifies the constructed H1 solution with a distributionally harmonic function, using
the retained metric volume. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the
project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarPotential_laplacian_pairing {Ω : Set Plane} (q : Plane → ℝ)
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hqc : HasCompactSupport q)
    (w : H1Zero D Ω) (f : EnergyTest D Ω) :
    (∫ x, scalarPotentialL2 D Ω q hq hqc w x * D.laplacian f x ∂g.volumeMeasure) =
      boundaryForcing D Ω q hq hqc f - gradientEnergy D Ω w f := by
  rw [← boundaryLaplacian_inner D f f.smooth f.hasCompactSupport]
  simp only [scalarPotentialL2, inner_add_right]
  have hqpair :
      ⟪boundaryLaplacianL2 D f f.smooth f.hasCompactSupport,
        (hq.continuous.memLp_of_hasCompactSupport hqc).toLp q⟫_ℝ =
      boundaryForcing D Ω q hq hqc f := by
    rw [boundaryLaplacian_inner, boundaryForcing_coe]
    calc
      _ = ∫ x, q x * D.laplacian f x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [(hq.continuous.memLp_of_hasCompactSupport hqc).coeFn_toLp]
          with x hx
        rw [hx]
      _ = _ := D.integral_mul_laplacian_comm_of_hasCompactSupport_left hq f.smooth hqc
  rw [hqpair]
  change _ + boundaryForcing D Ω f f.smooth f.hasCompactSupport w = _
  rw [boundaryForcing_test_source, sub_eq_add_neg]

/-- Every smooth metric on the plane has a genuine scalar weakly harmonic annular potential
with the 0/1 boundary extension, and the same constructed correction minimizes affine
Dirichlet energy. No uniformization certificate or candidate harmonic map is a hypothesis.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-dirichlet.md`; scalar boundary
and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem exists_annular_distributional_harmonic_potential :
    ∃ (U : Lp ℝ 2 g.volumeMeasure) (w : H1Zero D scalarAnnulus),
      U = scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w ∧
      (∀ f : EnergyTest D scalarAnnulus,
        (∫ x, U x * D.laplacian f x ∂g.volumeMeasure) = 0) ∧
      ∀ v : H1Zero D scalarAnnulus,
        affineDirichletEnergy D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w ≤
        affineDirichletEnergy D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact v := by
  obtain ⟨w, hw, hmin⟩ := exists_annular_harmonic_potential D
  refine ⟨scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
    annularBoundaryExtension_smooth annularBoundaryExtension_compact w, w, rfl, ?_, hmin⟩
  intro f
  rw [scalarPotential_laplacian_pairing, boundaryForcing_eq_neg_gradient]
  linarith [hw f]

end PoincareMT.M64Uniformization
