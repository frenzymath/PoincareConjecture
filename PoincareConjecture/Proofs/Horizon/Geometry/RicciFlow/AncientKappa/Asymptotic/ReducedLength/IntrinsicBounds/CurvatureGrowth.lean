import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.PathValues
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem reducedLength_intrinsic_quadratic_upper_bound
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M) {τ : ℝ} (hτ : 0 < τ) :
    reducedLength K.flow 0 p y τ ≤ 2 * reducedLength K.flow 0 p x τ +
      24 * ((K.flow.metric (0 - τ)).edist x y).toReal ^ 2 / τ := by
  apply (P.reducedLength_intrinsic_upper_bound p x y hτ).trans
  have hl := Real.sq_sqrt (P.reducedLength_pos p x τ hτ).le
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 3 / τ)
  have h := sq_nonneg (Real.sqrt (reducedLength K.flow 0 p x τ) -
    (2 * Real.sqrt (3 / τ)) * ((K.flow.metric (0 - τ)).edist x y).toReal)
  simp only [div_eq_mul_inv] at *
  nlinarith [congrArg (fun a : ℝ => a * ((K.flow.metric (0 - τ)).edist x y).toReal ^ 2) hs]

theorem scalar_intrinsic_quadratic_upper_bound
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M) {τ : ℝ} (hτ : 0 < τ) :
    (K.flow.connection (0 - τ)).scalarCurvature y ≤
      6 * reducedLength K.flow 0 p x τ / τ +
        72 * ((K.flow.metric (0 - τ)).edist x y).toReal ^ 2 / τ ^ 2 := by
  apply (P.scalar_le_reducedLength p y τ hτ).trans
  have h := mul_le_mul_of_nonneg_left
    (P.reducedLength_intrinsic_quadratic_upper_bound p x y hτ)
    (by positivity : 0 ≤ 3 / τ)
  convert! h using 1 <;> ring

theorem ricci_intrinsic_quadratic_upper_bound
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M) {τ : ℝ} (hτ : 0 < τ)
    (v : TangentSpace (𝓡 n) y) :
    (K.flow.connection (0 - τ)).ricci y v v ≤
      (6 * reducedLength K.flow 0 p x τ / τ +
        72 * ((K.flow.metric (0 - τ)).edist x y).toReal ^ 2 / τ ^ 2) *
          (K.flow.metric (0 - τ)).inner y v v := by
  have hRic := (K.flow.connection (0 - τ)).ricci_bounds_of_nonnegative_curvatureOperator
    (K.flow.connection (0 - τ)).intrinsicCurvatureTensorCalculus y
    (K.nonnegative_curvature_operator (0 - τ) (by linarith) y) v
  apply hRic.2.trans
  apply mul_le_mul_of_nonneg_right (P.scalar_intrinsic_quadratic_upper_bound p x y hτ)
  by_cases hv : v = 0
  · simp [hv]
  · exact ((K.flow.metric (0 - τ)).pos y v hv).le

theorem regular_path_scalar_quadratic_upper_bound
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z : TangentSpace (𝓡 n) p} {τ s : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hs : 0 < s) (hsτ : s ≤ τ) (y : M) :
    (K.flow.connection (0 - s)).scalarCurvature y ≤
      6 * (reducedLength K.flow 0 p (G.gamma Z τ) τ * Real.sqrt τ) /
        (s * Real.sqrt s) +
      72 * ((K.flow.metric (0 - s)).edist (G.gamma Z s) y).toReal ^ 2 / s ^ 2 := by
  apply (P.scalar_intrinsic_quadratic_upper_bound p (G.gamma Z s) y hs).trans
  refine add_le_add ?_ le_rfl
  have h := P.regular_path_reducedLength_mul_sqrt_le G hreg hs hsτ
  apply (div_le_div_iff₀ hs (mul_pos hs (Real.sqrt_pos.mpr hs))).mpr
  nlinarith [mul_le_mul_of_nonneg_left h hs.le]

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
