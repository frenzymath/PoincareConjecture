import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarMaximum












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)






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

end PoincareConjecture.M64Uniformization
