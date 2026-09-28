import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Periodic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Tolerance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {n : ℕ} [NeZero n]

theorem exists_ambient_isotopy_of_polygon_family
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    (p : ℝ → Polygon E n) (hp : ∀ i, ContDiff ℝ ∞ (fun t => p t i))
    {a b : ℝ} (hab : a ≤ b) (hsimple : ∀ t ∈ Icc a b, IsSimplePolygon (p t)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∃ ρ : ℝ → ℝ,
      ContDiff ℝ ∞ ρ ∧ (∀ s, δ ≤ |s| → ρ s = |s|) ∧
      (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) ∧ (∀ s, |deriv ρ s| ≤ 1) ∧
      ∃ Phi : ℝ → E ≃ₘ[ℝ] E,
        (∀ x, Phi a x = x) ∧ ContDiff ℝ ∞ (fun x : ℝ × E => Phi x.1 x.2) ∧
        (∃ K : Set E, IsCompact K ∧ ∀ t x, x ∉ K → Phi t x = x) ∧
        ∀ t ∈ Icc a b,
          Phi t '' range (roundedPolygonParameter ρ (p a)) =
            range (roundedPolygonParameter ρ (p t)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨δ, hδ, hδsmall, ρ, hρ, htail, hbound, hder, hγ, hper, hinj, hregular, _⟩ :=
    exists_smooth_rounded_polygon_family isCompact_Icc p hp hsimple (ε := 1) zero_lt_one
  exact ⟨δ, hδ, hδsmall, ρ, hρ, htail, hbound, hder,
    exists_ambient_isotopy_of_periodic_family e o hn hab
      (fun t => roundedPolygonParameter ρ (p t)) hγ hper hinj hregular⟩

theorem exists_uniform_ambient_isotopy_of_polygon_family
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    (p : ℝ → Polygon E n) (hp : ∀ i, ContDiff ℝ ∞ (fun t => p t i))
    {a b : ℝ} (hab : a ≤ b) (hsimple : ∀ t ∈ Icc a b, IsSimplePolygon (p t)) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 4 ∧
      ∀ δ : ℝ, 0 < δ → δ < d → ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ →
        (∀ s, δ ≤ |s| → ρ s = |s|) →
        (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) → (∀ s, |deriv ρ s| ≤ 1) →
        ∃ Phi : ℝ → E ≃ₘ[ℝ] E,
          (∀ x, Phi a x = x) ∧ ContDiff ℝ ∞ (fun x : ℝ × E => Phi x.1 x.2) ∧
          (∃ K : Set E, IsCompact K ∧ ∀ t x, x ∉ K → Phi t x = x) ∧
          ∀ t ∈ Icc a b,
            Phi t '' range (roundedPolygonParameter ρ (p a)) =
              range (roundedPolygonParameter ρ (p t)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨d, hd, hdsmall, htolerance⟩ := exists_uniform_rounding_tolerance isCompact_Icc
    p (fun i => (hp i).continuous) hsimple (ε := 1) zero_lt_one
  refine ⟨d, hd, hdsmall, ?_⟩
  intro δ hδ hδd ρ hρ htail hbound hder
  obtain ⟨hinj, hregular, _⟩ := htolerance δ hδ hδd ρ hρ htail hbound hder
  exact exists_ambient_isotopy_of_periodic_family e o hn hab
    (fun t => roundedPolygonParameter ρ (p t))
    (contDiff_roundedPolygonParameter hδ (by linarith) htail hbound hρ hp)
    (fun _ => periodic_roundedPolygonParameter _ _) hinj hregular

end Poincare.Manifold.Schoenflies.Plane
