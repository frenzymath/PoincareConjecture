import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionIntegrability

set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

theorem m64AnnulusDomain_boundary_null :
    volume (m64AnnulusDomain \ interior m64AnnulusDomain) = 0 := by
  let e : LoopPlane → (Fin 2 → ℝ) := @WithLp.ofLp 2 (Fin 2 → ℝ)
  let lo : Fin 2 → ℝ := 0
  let hi : Fin 2 → ℝ := ![curvePeriod, 1]
  let S : Set LoopPlane := e ⁻¹' (Set.pi Set.univ
    (fun i : Fin 2 => Set.Ioo (lo i) (hi i)))
  have hS : IsOpen S := by
    apply (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage
    exact PiLp.continuous_ofLp 2 _
  have hSdom : S ⊆ m64AnnulusDomain := by
    intro p hp
    simp only [S, e, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Ioo] at hp
    change 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
    have h0 := hp 0 trivial
    have h1 := hp 1 trivial
    simpa [lo, hi] using ⟨h0.1.le, h0.2.le, h1.1.le, h1.2.le⟩
  have hSint : S ⊆ interior m64AnnulusDomain :=
    interior_maximal hSdom hS
  have hae : m64AnnulusDomain =ᵐ[volume] S := by
    simpa only [S, e, lo, hi] using m64AnnulusDomain_ae_eq_boxInterior
  apply measure_mono_null _ (ae_eq_set.mp hae).1
  intro p hp
  exact ⟨hp.1, fun hpint => hp.2 (hSint hpint)⟩

end PoincareConjecture
