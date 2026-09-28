import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.DomainSupports
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.LeviCivitaData

theorem exists_liYau_bound_on_domains_containing_ball
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PreconnectedSpace M] {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (hn : 0 < n) (hcomplete : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    (O : M) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ Ω : Set M, IsOpen Ω →
      {z | (g.edist O z).toReal ≤ 5 * R} ⊆ Ω → ∀ u : ℝ × M → ℝ,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ Ω) →
      (∀ t, 0 < t → ∀ x ∈ Ω, 0 < u (t, x)) →
      (∀ t, 0 < t → ∀ x ∈ Ω, HasDerivAt (fun s => u (s, x))
        (D.laplacian (fun y => u (t, y)) x) t) →
      ∀ t, 0 < t → ∀ x, (g.edist O x).toReal ≤ R →
        g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
          (D.gradient (fun y => Real.log (u (t, y))) x) -
          2 * deriv (fun s => Real.log (u (s, x))) t ≤ 4 * (n : ℝ) / t + C := by
  obtain ⟨η, B, hB, hηs, hηc, hη, hone, hsupport, hgrad, hlap⟩ :=
    D.exists_intrinsic_ball_cutoff_laplacian_bound hcomplete O hR
  let A := 4 * (heatCutoffConstant / R) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := 4 * (n : ℝ) * (B + ((n : ℝ) + 2) * A + k)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Ω hΩ hcontains u hu hpos hheat t ht x hx
  have hxΩ : x ∈ Ω := hcontains (show (g.edist O x).toReal ≤ 5 * R by linarith)
  have h := D.liYau_cutoff_bound_of_lower_supports_on hn hk hA hB.le hRic hΩ hu hpos hheat
    hηs.continuous hηc (hsupport.trans hcontains) hη (fun y _ => ?_) t ht x hxΩ
  · rw [hone x hx, mul_one] at h
    apply (mul_le_mul_iff_right₀ ht).mp
    have he : t * (4 * (n : ℝ) / t + C) =
        4 * (n : ℝ) * (1 + (B + ((n : ℝ) + 2) * A + k) * t) := by
      dsimp [C]
      field_simp
    rw [he]
    exact h
  · exact ⟨univ, η, isOpen_univ, mem_univ y, hηs.contMDiffOn, rfl,
      fun _ _ => le_rfl, hgrad y, (abs_le.mp (hlap y)).1⟩

end PoincareConjecture.LeviCivitaData
