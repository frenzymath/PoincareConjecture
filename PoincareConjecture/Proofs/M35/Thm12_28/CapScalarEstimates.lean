import PoincareConjecture.Definitions.M35StandardCapUniqueness
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Gradient

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

theorem abs_scalar_directional_le_scalarGradientNorm
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 3) x) (hv : g.inner x v v = 1) :
    |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤ scalarGradientNorm g D x := by
  unfold scalarGradientNorm
  refine le_csSup (s := range (fun w : {w // g.inner x w w = 1} =>
    |mvfderiv (𝓡 3) D.scalarCurvature x w.val|)) ?_ ⟨⟨v, hv⟩, rfl⟩
  refine ⟨g.tangentNorm x (D.gradient D.scalarCurvature x), ?_⟩
  rintro z ⟨⟨w, hw⟩, rfl⟩
  have h := D.abs_mvfderiv_le_gradient_norm D.scalarCurvature x w
  have hn : g.tangentNorm x w = 1 := by
    change Real.sqrt (g.inner x w w) = 1
    rw [hw, Real.sqrt_one]
  simpa only [hn, mul_one] using h

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.StandardCapNeighborhood

theorem scalar_analytic_bounds {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t epsilon C : ℝ} {x : StandardCapSpace}
    (N : StandardCapNeighborhood atlas F t epsilon C x) :
    (∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
      |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| <
        C * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
    |(F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x| < C * ((F.connection t).scalarCurvature x) ^ 2 := by
  have hx : x ∈ N.carrier := by
    have hcore := interior_subset N.center_in_core
    rw [N.closed_core_eq] at hcore
    exact hcore.1
  refine ⟨?_, N.time_derivative_bound x hx⟩
  intro v hv
  exact ((F.connection t).abs_scalar_directional_le_scalarGradientNorm x v hv).trans_lt
    (N.gradient_bound x hx)

end PoincareConjecture.StandardCapNeighborhood

namespace PoincareConjecture.M35

theorem capCertificate_scalar_analytic_bounds
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g) {x : M} (hx : x ∈ N.core) :
    (∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
      |mvfderiv (𝓡 3) N.connection.scalarCurvature x v| ≤
        N.cap_constant * N.connection.scalarCurvature x ^ (3 / 2 : ℝ)) ∧
    |N.connection.laplacian N.connection.scalarCurvature x +
        2 * N.connection.ricciNormSq x| ≤
      N.cap_constant * (N.connection.scalarCurvature x) ^ 2 := by
  have hxU : x ∈ N.carrier := by
    rw [N.core_eq_interior_closed_core] at hx
    have hclosed := interior_subset hx
    rw [N.closed_core_eq_complement_end] at hclosed
    exact hclosed.1
  obtain ⟨B, hB, hgrad⟩ := N.gradient_bound
  obtain ⟨D, hD, htime⟩ := N.laplacian_bound
  constructor
  · intro v hv
    exact (N.connection.abs_scalar_directional_le_scalarGradientNorm x v hv).trans
      ((hgrad x hxU).trans (mul_le_mul_of_nonneg_right hB.le
        (Real.rpow_nonneg (N.scalar_pos x hxU).le _)))
  · exact (htime x hxU).trans (mul_le_mul_of_nonneg_right hD.le (sq_nonneg _))

end PoincareConjecture.M35
