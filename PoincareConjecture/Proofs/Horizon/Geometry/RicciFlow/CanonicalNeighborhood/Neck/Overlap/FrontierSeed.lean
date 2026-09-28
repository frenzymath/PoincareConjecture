import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ReciprocalStrip

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_frontier_axial_seed_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        ∀ x : M, x ∈ frontier N.carrier →
        x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        x ∈ P.central_sphere →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          (∀ (q : UnitTwoSphere) (t : ℝ),
            t ∈ Ioo (-(0.08 : ℝ) * N.epsilon⁻¹) (-(0.02 : ℝ) * N.epsilon⁻¹) →
            P.coordinate_map (q, σ * t) ∈
              N.region ((0.9 : ℝ) * N.epsilon⁻¹) ((0.99 : ℝ) * N.epsilon⁻¹)) ∧
          ∀ q : UnitTwoSphere,
            (N.coordinate_inverse (P.coordinate_map (q, σ * (-(0.07 : ℝ) * N.epsilon⁻¹)))).2 <
              (N.coordinate_inverse (P.coordinate_map (q, σ * (-(0.03 : ℝ) * N.epsilon⁻¹)))).2 := by
  obtain ⟨ε₁, hε₁, _, hheight⟩ := exists_frontier_transition_height_bounds.{u}
  obtain ⟨ε₂, hε₂, _, hcontain⟩ :=
    exists_closure_positive_quarter_subset_of_central_sphere_contact.{u}
  refine ⟨min ε₁ (min ε₂ (1 / 10000)), lt_min hε₁ (lt_min hε₂ (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq x hxfront hx hxP
  have hsmall := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨σ, hσ, hh⟩ := hheight N P (hε.trans (min_le_left _ _)) heq x hxfront hx hxP
  have hquarter := hcontain N P
    (hε.trans ((min_le_right _ _).trans (min_le_left _ _))) heq ⟨x, hx, hxP⟩
  have hstrip := N.signed_strip_subset_of_frontier_height_bounds P heq hsmall hquarter hσ hh
  let R := N.epsilon⁻¹
  have hR : 0 < R := inv_pos.mpr N.epsilon_pos
  have hlarge : (10000 : ℝ) ≤ R := by
    change 10000 ≤ N.epsilon⁻¹
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith
  have hdom {t : ℝ} (ht : t ∈ Ioo (-(0.08 : ℝ) * R) (-(0.02 : ℝ) * R))
      (q : UnitTwoSphere) : (q, σ * t) ∈ P.cylinderDomain := by
    refine ⟨mem_univ _, ?_⟩
    rw [heq]
    rcases hσ with rfl | rfl <;> constructor <;> nlinarith [ht.1, ht.2]
  have hsq (t : ℝ) : σ * (σ * t) = t := by
    rcases hσ with rfl | rfl <;> ring
  have hinside (q : UnitTwoSphere) (t : ℝ)
      (ht : t ∈ Ioo (-(0.08 : ℝ) * R) (-(0.02 : ℝ) * R)) :
      P.coordinate_map (q, σ * t) ∈ N.region ((0.9 : ℝ) * R) ((0.99 : ℝ) * R) := by
    apply hstrip
    refine ⟨P.coordinate_map_mem (hdom ht q), ?_⟩
    rw [P.coordinate_inverse_coordinate_map (hdom ht q), hsq]
    exact ht
  refine ⟨σ, hσ, hinside, ?_⟩
  intro q
  have hbounds (t : ℝ) (ht : t ∈ Ioo (-(0.08 : ℝ) * R) (-(0.02 : ℝ) * R)) :
      -(1.1 : ℝ) * (R - (N.coordinate_inverse (P.coordinate_map (q, σ * t))).2) - 5 * Real.pi ≤ t ∧
        t ≤ -(0.9 : ℝ) * (R - (N.coordinate_inverse (P.coordinate_map (q, σ * t))).2) + 5 * Real.pi := by
    let y := P.coordinate_map (q, σ * t)
    have hy := hinside q t ht
    have ha : (N.coordinate_inverse y).2 ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
      constructor <;> linarith [hy.2.1, hy.2.2]
    have h := hh (N.coordinate_inverse y).1 (N.coordinate_inverse y).2 ha
    rw [N.coordinate_map_coordinate_inverse hy.1] at h
    dsimp [y] at h
    rw [P.coordinate_inverse_coordinate_map (hdom ht q), hsq] at h
    exact h
  have h₁ := (hbounds (-(0.07 : ℝ) * R) (by constructor <;> linarith)).1
  have h₂ := (hbounds (-(0.03 : ℝ) * R) (by constructor <;> linarith)).2
  change (N.coordinate_inverse (P.coordinate_map (q, σ * (-(0.07 : ℝ) * R)))).2 <
    (N.coordinate_inverse (P.coordinate_map (q, σ * (-(0.03 : ℝ) * R)))).2
  nlinarith [Real.pi_le_four]

end PoincareConjecture.EpsilonNeck
