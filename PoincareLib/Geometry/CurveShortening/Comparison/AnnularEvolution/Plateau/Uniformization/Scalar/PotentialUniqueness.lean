import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.Maximum

/-!
# Uniqueness of the actual classical annular Dirichlet potential

The proved scalar maximum principle compares two genuine harmonic
potentials. In particular, the boundary-regular potential and the potential
used by the covering chart agree on the entire closed annulus.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- Boundary comparison extends throughout the closed annulus for actual continuous harmonic
potentials. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project
construction in `proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-maximum.md`;
scalar boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem annular_harmonic_comparison {H K : Plane → ℝ}
    (hHc : Continuous H) (hKc : Continuous K)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hKs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ K scalarAnnulus)
    (hHlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hKlap : ∀ x ∈ scalarAnnulus, D.laplacian K x = 0)
    (hboundary : ∀ x, scalarAnnulusDefining x = 0 → H x ≤ K x) :
    ∀ x, 0 ≤ scalarAnnulusDefining x → H x ≤ K x := by
  have h := annular_subharmonic_le_boundary D (hHc.sub hKc) (hHs.sub hKs)
    (C := 0) (by
      intro x hx
      obtain ⟨U, hUs, -, -, hUH⟩ := exists_compact_smooth_germ scalarAnnulus_isOpen hHs hx
      obtain ⟨V, hVs, -, -, hVK⟩ := exists_compact_smooth_germ scalarAnnulus_isOpen hKs hx
      have heq : (fun y => U y - V y) =ᶠ[𝓝 x] (fun y => H y - K y) := by
        filter_upwards [hUH, hVK] with y hy hy'
        rw [hy, hy']
      change 0 ≤ D.laplacian (fun y => H y - K y) x
      rw [← D.laplacian_eq_of_eventuallyEq heq, D.laplacian_sub hUs hVs,
        D.laplacian_eq_of_eventuallyEq hUH, D.laplacian_eq_of_eventuallyEq hVK,
        hHlap x hx, hKlap x hx, sub_self])
    (fun x hx => sub_nonpos.mpr (hboundary x hx))
  intro x hx
  exact sub_nonpos.mp (h x hx)

/-- The actual annular potential is unique for its two classical boundary values,
independently of which proved construction produced it. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-maximum.md`; scalar boundary and
energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem annular_harmonic_eq_on_closed {H K : Plane → ℝ}
    (hHc : Continuous H) (hKc : Continuous K)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hKs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ K scalarAnnulus)
    (hHlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hKlap : ∀ x ∈ scalarAnnulus, D.laplacian K x = 0)
    (hboundary : ∀ x, scalarAnnulusDefining x = 0 → H x = K x) :
    EqOn H K {x : Plane | 0 ≤ scalarAnnulusDefining x} := by
  have hHK := annular_harmonic_comparison D hHc hKc hHs hKs hHlap hKlap
    (fun x hx => (hboundary x hx).le)
  have hKH := annular_harmonic_comparison D hKc hHc hKs hHs hKlap hHlap
    (fun x hx => (hboundary x hx).ge)
  intro x hx
  exact le_antisymm (hHK x hx) (hKH x hx)

end PoincareMT.M64Uniformization
