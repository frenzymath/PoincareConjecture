import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Deletion.Approximation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Deletion.Interpolation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Deletion.PeriodicWindows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {n : ℕ}

theorem exists_uniform_ambient_delete_last_midpoint
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    {p : Polygon E (n + 4)} (hp : IsSimplePolygon p)
    (hmid : p (Fin.last (n + 3)) =
      midpoint ℝ (p (Fin.last (n + 2)).castSucc) (p 0)) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 8 ∧
      ∀ δ : ℝ, 0 < δ → δ < d → ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ →
        (∀ s, δ ≤ |s| → ρ s = |s|) →
        (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) → (∀ s, |deriv ρ s| ≤ 1) →
        ∃ F : E ≃ₘ[ℝ] E,
          (∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
          F '' range (roundedPolygonParameter ρ p) =
            range (roundedPolygonParameter ρ (polygonDeleteVertex p (Fin.last (n + 3)))) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  obtain ⟨η, hη, htransport⟩ := exists_ambient_polygon_interpolation_tolerance e o hp
  let B : ℝ := (∑ i : Fin (n + 4), ‖p i‖) + 1
  have hB0 : 0 < B := by
    dsimp [B]
    positivity
  have hB (i : Fin (n + 4)) : ‖p i‖ ≤ B := by
    have hi : ‖p i‖ ≤ ∑ j : Fin (n + 4), ‖p j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (p j)) (Finset.mem_univ i)
    dsimp [B]
    linarith
  let d : ℝ := min (1 / 16) (η / (6 * B))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hη (by positivity))
  have hdsmall : d < 1 / 8 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨d, hd, hdsmall, ?_⟩
  intro δ hδ hδd ρ hρ htail hbound hder
  have hδsmall : δ < 1 / 8 := hδd.trans hdsmall
  have hhalf : δ < 1 / 2 := by linarith
  have herr : 3 * δ * B < η := by
    have hlt : δ < η / (6 * B) := hδd.trans_le (min_le_right _ _)
    have hmul := (lt_div_iff₀ (show 0 < 6 * B by positivity)).mp hlt
    nlinarith [mul_pos hδ hB0]
  let q := polygonDeleteVertex p (Fin.last (n + 3))
  let α := roundedPolygonParameter ρ p
  let β := fun t => roundedPolygonParameter ρ q (deletionClock ρ (n + 4) t)
  have hα : ContDiff ℝ ∞ α :=
    contDiff_roundedPolygonParameter_const p hδ hhalf htail hbound hρ
  have hq : ContDiff ℝ ∞ (roundedPolygonParameter ρ q) :=
    contDiff_roundedPolygonParameter_const q hδ hhalf htail hbound hρ
  have hclock := contDiff_deletionClock (n + 4) hδ hhalf htail hbound hρ
  have hβ : ContDiff ℝ ∞ β := hq.comp hclock
  have hαper : Periodic α (n + 4 : ℕ) := periodic_roundedPolygonParameter ρ p
  have hβper : Periodic β (n + 4 : ℕ) := by
    intro t
    dsimp [β]
    rw [deletionClock_add_period ρ (show 0 < n + 4 by omega)]
    have heq : deletionClock ρ (n + 4) t + ((n + 4 : ℕ) : ℝ) - 1 =
        deletionClock ρ (n + 4) t + ((n + 3 : ℕ) : ℝ) := by push_cast; ring
    rw [heq]
    exact periodic_roundedPolygonParameter ρ q _
  have hαclose (t : ℝ) (_ht : t ∈ Icc 0 ((n + 4 : ℕ) : ℝ)) :
      dist (α t) (polygonLinearParameter p t) < η := by
    exact (dist_roundedPolygonParameter_le p hδ hhalf htail hbound hB t).trans_lt (by
      nlinarith [mul_pos hδ hB0])
  have hβclose (t : ℝ) (ht : t ∈ Icc 0 ((n + 4 : ℕ) : ℝ)) :
      dist (β t) (polygonLinearParameter p t) < η :=
    (dist_roundedPolygon_delete_last_clock_le p hmid hδ hhalf htail hbound hρ hder hB ht).trans_lt herr
  have hwindow : ∀ i : ℤ, ∃ ℓ : E →L[ℝ] ℝ, ∀ t : ℝ, |t - (i : ℝ)| < 3 / 4 →
      0 < ℓ (deriv α t) ∧ 0 < ℓ (deriv β t) := by
    apply exists_positive_derivatives_on_integer_window_of_periodic
      (n := n + 4) (by omega) (hα.differentiable (by simp)) (hβ.differentiable (by simp)) hαper hβper
    intro i hi hin
    exact exists_positive_deletion_derivatives_on_finite_window hp hmid
      hδ hδsmall htail hbound hρ hder i hi (by exact_mod_cast hin)
  obtain ⟨F, hFcompact, hF⟩ := htransport α β hα hβ hαper hβper hαclose hβclose hwindow
  refine ⟨F, hFcompact, hF.trans ?_⟩
  have hsurj := surjective_deletionClock (N := n + 4) (by omega) hδ hhalf htail hbound hρ
  change range ((roundedPolygonParameter ρ q) ∘ deletionClock ρ (n + 4)) =
    range (roundedPolygonParameter ρ q)
  exact hsurj.range_comp _

end Poincare.Manifold.Schoenflies.Plane
