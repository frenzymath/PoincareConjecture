import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.DomainResolvent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.WeakEquation

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

theorem resolvent_oneSubLaplacian_of_local_green (f : EnergyTest D Ω) :
    resolvent D Ω f.oneSubLaplacian = (f : H1Zero D Ω) := by
  apply ext_inner_right ℝ
  intro u
  rw [resolvent_inner, inner_test_eq_oneSubLaplacian]

theorem toL2_injective_of_local_green : Function.Injective (toL2 D Ω) := by
  suffices hzero : ∀ u : H1Zero D Ω, toL2 D Ω u = 0 → u = 0 from
    fun u v huv => sub_eq_zero.mp (hzero (u - v) (by simpa using sub_eq_zero.mpr huv))
  intro u hu
  have hall (v : H1Zero D Ω) : ⟪v, u⟫_ℝ = 0 := by
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
    | ih v => rw [inner_test_eq_oneSubLaplacian, hu, inner_zero_right]
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hall u)

theorem toDomainL2_injective_of_local_green (hΩ : MeasurableSet Ω) :
    Function.Injective (toDomainL2 D Ω) := by
  intro u v huv
  apply toL2_injective_of_local_green
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← map_sub, ← norm_toDomainL2 hΩ, map_sub, huv, sub_self, norm_zero]

theorem domainResolvent_oneSubLaplacian (hΩ : MeasurableSet Ω) (f : EnergyTest D Ω) :
    domainResolvent D Ω
      (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω f.oneSubLaplacian) =
      (f : H1Zero D Ω) := by
  rw [domainResolvent_restrict hΩ, resolvent_oneSubLaplacian_of_local_green]

theorem denseRange_domainResolvent (hΩ : MeasurableSet Ω) :
    DenseRange (domainResolvent D Ω) := by
  apply Completion.denseRange_coe.mono
  rintro _ ⟨f, rfl⟩
  exact ⟨LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω f.oneSubLaplacian,
    domainResolvent_oneSubLaplacian hΩ f⟩

theorem inner_energy_test_eq_domain_integral (hΩ : MeasurableSet Ω)
    (u : H1Zero D Ω) (φ : EnergyTest D Ω) :
    ⟪u, (φ : H1Zero D Ω)⟫_ℝ =
      ∫ x in Ω, (φ x - D.laplacian φ x) * toDomainL2 D Ω u x ∂g.volumeMeasure := by
  rw [real_inner_comm, inner_test_eq_oneSubLaplacian,
    ← inner_restrict_toDomainL2 hΩ, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ Ω φ.oneSubLaplacian,
    ae_restrict_of_ae φ.oneSubLaplacian_memLp.coeFn_toLp] with x hx hy
  rw [hx, show φ.oneSubLaplacian x = φ x - D.laplacian φ x from hy]
  simp [mul_comm]

end PoincareConjecture.LeviCivitaData.Dirichlet
