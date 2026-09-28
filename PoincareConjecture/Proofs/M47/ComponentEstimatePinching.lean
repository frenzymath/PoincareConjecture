import PoincareConjecture.Proofs.M47.SeedVolume











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}



theorem component_pinched_curvature_bound (P : M47Predecessors.{u})
    {t Q L : ℝ} {U : Set M} (hpinch : SurgeryPinchedOn D t U)
    (hQ : Real.exp 4 ≤ Q) (hL : 1 ≤ L) {x : M} (hx : x ∈ U)
    (hscalar : D.scalarCurvature x ≤ L * Q) :
    D.curvatureTensorNorm x ≤ 13 * (L * Q) := by
  have hQpos : 0 < Q := (Real.exp_pos 4).trans_le hQ
  have hQL : Q ≤ L * Q := by nlinarith
  exact (Proofs.M46.pinched_curvature_norm_le P.toM46 hpinch hx).trans
    (mul_le_mul_of_nonneg_left (max_le hscalar (hQ.trans hQL)) (by norm_num))



theorem component_pinched_scalar_floor {t : ℝ} {U : Set M}
    (hpinch : SurgeryPinchedOn D t U) {x : M} (hx : x ∈ U) :
    -6 ≤ D.scalarCurvature x := by
  have hden : 0 < 1 + 4 * t := by linarith [hpinch.1]
  have hfloor : (-6 : ℝ) ≤ -6 / (1 + 4 * t) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hpinch.1]
  exact hfloor.trans (hpinch.2.1 x hx)



theorem component_pinched_scaled_scalar_floor {t Q L : ℝ} {U : Set M}
    (hpinch : SurgeryPinchedOn D t U) (hQ : 6 ≤ Q) (hL : 1 ≤ L)
    {x : M} (hx : x ∈ U) : -(L * Q) ≤ D.scalarCurvature x := by
  have hQL : 6 ≤ L * Q := by nlinarith
  exact (by linarith : -(L * Q) ≤ -6).trans (component_pinched_scalar_floor hpinch hx)

end PoincareConjecture.M47
