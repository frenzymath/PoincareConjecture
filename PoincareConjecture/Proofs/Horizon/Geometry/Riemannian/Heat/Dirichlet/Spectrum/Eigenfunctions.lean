import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.DomainResolvent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.WeakEquation












set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem domainResolvent_eigenvalue_pos (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    {μ : ℝ} {f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)} (hf : f ≠ 0)
    (he : domainL2Resolvent D Ω f = μ • f) : 0 < μ := by
  have hpos := domainL2Resolvent_pos (D := D) hΩ hc hf
  rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq] at hpos
  exact (mul_pos_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hf))).mp hpos

theorem domainResolvent_eigenvalue_le_one
    {μ : ℝ} {f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)} (hf : f ≠ 0)
    (he : domainL2Resolvent D Ω f = μ • f) : μ ≤ 1 := by
  have hnorm := norm_domainL2Resolvent_le (D := D) f
  rw [he, norm_smul, Real.norm_eq_abs] at hnorm
  have h := (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hf)).mp
    (show |μ| * ‖f‖ ≤ 1 * ‖f‖ by simpa using hnorm)
  exact (le_abs_self μ).trans h

theorem domainResolvent_lift_toDomainL2 {μ : ℝ} (hμ : μ ≠ 0)
    {f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)}
    (he : domainL2Resolvent D Ω f = μ • f) :
    toDomainL2 D Ω (μ⁻¹ • domainResolvent D Ω f) = f := by
  rw [map_smul]
  change μ⁻¹ • domainL2Resolvent D Ω f = f
  rw [he, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem domainResolvent_lift_weak_equation (hΩ : MeasurableSet Ω)
    {μ : ℝ} (hμ : μ ≠ 0) {f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)}
    (he : domainL2Resolvent D Ω f = μ • f) (v : H1Zero D Ω) :
    ⟪μ⁻¹ • domainResolvent D Ω f, v⟫_ℝ =
      (1 + (1 - μ) / μ) *
        ⟪toL2 D Ω (μ⁻¹ • domainResolvent D Ω f), toL2 D Ω v⟫_ℝ := by
  rw [← inner_toDomainL2 hΩ, domainResolvent_lift_toDomainL2 hμ he,
    real_inner_smul_left, domainResolvent_inner]
  congr 1
  field_simp
  ring



theorem exists_weak_eigenfunction_of_domainResolvent
    (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    {μ : ℝ} {f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)} (hf : f ≠ 0)
    (he : domainL2Resolvent D Ω f = μ • f) :
    0 ≤ (1 - μ) / μ ∧ ∃ u : H1Zero D Ω,
      toDomainL2 D Ω u = f ∧ u ≠ 0 ∧
      ∀ v : H1Zero D Ω, ⟪u, v⟫_ℝ =
        (1 + (1 - μ) / μ) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ := by
  have hμ := domainResolvent_eigenvalue_pos hΩ hc hf he
  have hlift := domainResolvent_lift_toDomainL2 hμ.ne' he
  refine ⟨div_nonneg (sub_nonneg.mpr (domainResolvent_eigenvalue_le_one hf he)) hμ.le,
    μ⁻¹ • domainResolvent D Ω f, hlift, ?_,
    domainResolvent_lift_weak_equation hΩ.measurableSet hμ.ne' he⟩
  intro hu
  exact hf (hlift.symm.trans (by rw [hu, map_zero]))

end PoincareConjecture.LeviCivitaData.Dirichlet
