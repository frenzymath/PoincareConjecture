import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Resolvent
import Mathlib.MeasureTheory.Integral.Bochner.Set










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

theorem restrict_compl_testToL2_eq_zero (hΩ : MeasurableSet Ω) (φ : EnergyTest D Ω) :
    LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ωᶜ (testToL2 D Ω φ) = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hφ : (testToL2 D Ω φ : M → ℝ) =ᵐ[g.volumeMeasure] φ := φ.memLp.coeFn_toLp
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ Ωᶜ (testToL2 D Ω φ),
    ae_restrict_of_ae hφ, ae_restrict_mem hΩ.compl]
    with x hx hval houtside
  rw [hx, hval]
  change φ x = 0
  exact image_eq_zero_of_notMem_tsupport (fun h => houtside (φ.support_subset h))

theorem restrict_compl_toL2_eq_zero (hΩ : MeasurableSet Ω) (u : H1Zero D Ω) :
    LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ωᶜ (toL2 D Ω u) = 0 := by
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ωᶜ).continuous.comp (toL2 D Ω).continuous)
      continuous_const
  | ih φ => simpa using restrict_compl_testToL2_eq_zero hΩ φ


theorem toL2_ae_zero_outside (hΩ : MeasurableSet Ω) (u : H1Zero D Ω) :
    ∀ᵐ x ∂g.volumeMeasure, x ∉ Ω → toL2 D Ω u x = 0 := by
  have h := (Lp.eq_zero_iff_ae_eq_zero.mp (restrict_compl_toL2_eq_zero hΩ u))
  have hres := LpToLpRestrictCLM_coeFn ℝ Ωᶜ (toL2 D Ω u)
  have hz : (toL2 D Ω u : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ωᶜ] 0 := hres.symm.trans h
  exact (ae_restrict_iff' hΩ.compl).mp hz


def toDomainL2 (D : LeviCivitaData g) (Ω : Set M) :
    H1Zero D Ω →L[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict Ω) :=
  (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω).comp (toL2 D Ω)

theorem toDomainL2_ae (u : H1Zero D Ω) :
    (toDomainL2 D Ω u : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω] toL2 D Ω u :=
  LpToLpRestrictCLM_coeFn ℝ Ω (toL2 D Ω u)

theorem norm_toDomainL2 (hΩ : MeasurableSet Ω) (u : H1Zero D Ω) :
    ‖toDomainL2 D Ω u‖ = ‖toL2 D Ω u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (toDomainL2_ae u), ← eLpNorm_indicator_eq_eLpNorm_restrict hΩ]
  apply eLpNorm_congr_ae
  filter_upwards [toL2_ae_zero_outside hΩ u] with x hx
  by_cases hxΩ : x ∈ Ω
  · simp [hxΩ]
  · simp [hxΩ, hx hxΩ]

theorem toDomainL2_injective [PreconnectedSpace M] (hΩ : MeasurableSet Ω) :
    Function.Injective (toDomainL2 D Ω) := by
  intro u v huv
  apply toL2_injective
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← map_sub, ← norm_toDomainL2 hΩ, map_sub, huv, sub_self, norm_zero]

end PoincareConjecture.LeviCivitaData.Dirichlet
