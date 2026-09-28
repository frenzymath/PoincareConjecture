import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem inner_gradient_sq_le (D : LeviCivitaData g) {χ : M → ℝ} {A : ℝ}
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hA : ∀ x, g.inner x (D.gradient χ x) (D.gradient χ x) ≤ A) (x : M) :
    g.inner x (D.gradient (fun y => χ y ^ 2) x)
      (D.gradient (fun y => χ y ^ 2) x) ≤ 4 * A * χ x ^ 2 := by
  have hd := (hχ x).mdifferentiableAt (by simp)
  have he : D.gradient (fun y => χ y ^ 2) x = (2 * χ x) • D.gradient χ x := by
    simp only [pow_two, D.gradient_mul hd hd]
    module
  rw [he]
  simp only [map_smul, smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left (hA x) (sq_nonneg (2 * χ x))]



theorem exists_abs_laplacian_bound (D : LeviCivitaData g) {η : M → ℝ}
    (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) (hc : HasCompactSupport η) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, |D.laplacian η x| ≤ B := by
  obtain ⟨B, hB⟩ := (D.hasCompactSupport_laplacian hc).exists_bound_of_continuous
    (D.continuous_laplacian hη)
  exact ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hB x).trans (le_max_right _ _)⟩



theorem exists_intrinsic_ball_cutoff_laplacian_bound [T3Space M] [PreconnectedSpace M]
    (D : LeviCivitaData g) (hcomplete : MetricComplete g) (O : M)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ η : M → ℝ, ∃ B : ℝ, 0 < B ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Icc 0 1) ∧
      (∀ x, (g.edist O x).toReal ≤ R → η x = 1) ∧
      (tsupport η ⊆ {x | (g.edist O x).toReal ≤ 5 * R}) ∧
      (∀ x, g.inner x (D.gradient η x) (D.gradient η x) ≤
        (4 * (heatCutoffConstant / R) ^ 2) * η x) ∧
      (∀ x, |D.laplacian η x| ≤ B) := by
  obtain ⟨χ, hχ, hc, hr, hone, hs, hg⟩ := D.exists_intrinsic_ball_cutoff hcomplete O hR
  let η := fun x => χ x ^ 2
  have hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η := by
    simpa only [η, pow_two, Pi.mul_def] using hχ.mul hχ
  have hcη : HasCompactSupport η := by
    simpa only [η, pow_two, Pi.mul_def] using (hc.mul_right : HasCompactSupport (χ * χ))
  obtain ⟨B, hB, hΔ⟩ := D.exists_abs_laplacian_bound hη hcη
  refine ⟨η, B, hB, hη, hcη, ?_, ?_, ?_, ?_, hΔ⟩
  · intro x
    refine ⟨sq_nonneg _, ?_⟩
    dsimp [η]
    nlinarith [(hr x).1, (hr x).2]
  · intro x hx
    simp [η, hone x hx]
  · apply Subset.trans ?_ hs
    simpa only [η, pow_two] using (tsupport_mul_subset_left (f := χ) (g := χ))
  · exact D.inner_gradient_sq_le hχ hg

end PoincareConjecture.LeviCivitaData
