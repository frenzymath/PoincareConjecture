import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryRadial











set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem IsCompact.exists_frontier_radial_pole_of_linear_image
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C)
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)) {p : E} (hp : p ∈ C)
    {σ : ℝ} (hσ : σ ≠ 0) (hep : e p = ((0, σ), 0)) :
    ∃ (q : E) (ρ : ℝ), q ∈ frontier C ∧ 1 ≤ ρ ∧
      q = ρ • p ∧ e q = ((0, ρ * σ), 0) ∧ ρ * σ ≠ 0 ∧
      (p ∈ interior C → 1 < ρ) := by
  have hpne : p ≠ 0 := by
    intro hp0
    have h := hep
    rw [hp0, map_zero] at h
    have hσ0 : (0 : ℝ) = σ := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) h
    exact hσ hσ0.symm
  obtain ⟨q, hq, t, ht, hpq⟩ := hC.exists_frontier_pos_smul hcv hzero hp hpne
  have hρ : 1 ≤ t⁻¹ := (one_le_inv₀ ht.1).mpr ht.2
  have hqeq : q = t⁻¹ • p := by rw [hpq, inv_smul_smul₀ ht.1.ne']
  have heq : e q = ((0, t⁻¹ * σ), 0) := by
    rw [hqeq, map_smul, hep]
    ext <;> simp
  refine ⟨q, t⁻¹, hq, hρ, hqeq, heq, mul_ne_zero (inv_ne_zero ht.1.ne') hσ, ?_⟩
  intro hpint
  apply lt_of_le_of_ne hρ
  intro hρeq
  have hqp : q = p := by rw [hqeq, ← hρeq, one_smul]
  exact hq.2 (hqp.symm ▸ hpint)
