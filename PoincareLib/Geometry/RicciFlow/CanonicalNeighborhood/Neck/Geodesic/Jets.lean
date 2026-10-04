import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Jet
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Frame
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Evaluation

/-!
# First metric jets in an epsilon-neck

The frozen neck comparison bounds every individual normalized covariant jet,
not only the finite jet sum appearing in `RoundCylinderClose`.  In the
canonical chart basis this gives the multilinear estimate used in geodesic
equation stability.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.EpsilonNeck

local instance : Bundle.RiemannianBundle
    (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
  ⟨roundCylinderProductMetric.toRiemannianMetric⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- Every individual normalized cylinder jet is bounded by the full neck jet
sum.  The bound is uniform in the order as long as that order is stored in
the frozen comparison. -/
theorem normalized_pullback_iterated_normSquared_lt
    (N : EpsilonNeck g) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {k : ℕ} (hk : k ≤ ⌊N.epsilon⁻¹⌋₊) :
    roundCylinderTensorNormSquared 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          N.normalized_pullback k
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) < N.epsilon ^ 2 := by
  rcases N.normalized_pullback_close with ⟨_, ⟨bound, hbound, hjet⟩⟩
  have hterm :
      roundCylinderTensorNormSquared 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
          (roundCylinderIteratedDerivative 0
            (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
            N.normalized_pullback k
            (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) ≤
        roundCylinderJetErrorSquared 0 N.normalized_pullback
          ⌊N.epsilon⁻¹⌋₊ z := by
    dsimp only [roundCylinderJetErrorSquared]
    apply Finset.single_le_sum (f := fun j =>
      roundCylinderTensorNormSquared 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          N.normalized_pullback j
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)))
    · intro j hj
      exact roundCylinderTensorNormSquared_nonneg z.1
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          N.normalized_pullback j
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2))
    · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  exact lt_of_le_of_lt hterm (lt_of_le_of_lt (hjet z hz) hbound)

/-- The existing upper bound on neck epsilon always retains the first
normalized covariant derivative in the frozen jet comparison. -/
theorem normalized_pullback_first_derivative_normSquared_lt
    (N : EpsilonNeck g) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    roundCylinderTensorNormSquared 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          N.normalized_pullback 1
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) < N.epsilon ^ 2 := by
  apply N.normalized_pullback_iterated_normSquared_lt hz
  apply (Nat.one_le_floor_iff _).mpr
  exact (one_le_inv₀ N.epsilon_pos).mpr
    (le_trans (le_of_lt N.epsilon_lt_half) (by norm_num))

/-- The first normalized metric jet controls evaluation on arbitrary three
tangent vectors in the frozen cylinder metric. -/
theorem normalized_pullback_first_derivative_apply_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : Fin 3 → RoundCylinderTangent
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q), s)) :
    |componentMultilinearMap
      (roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        N.normalized_pullback 1
          (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s))
      (roundCylinderChartBasis q (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s)) v| ≤
      N.epsilon * ∏ r, ‖v r‖ := by
  let b := roundCylinderChartBasis q
    (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s)
  let : FiniteDimensional ℝ
      (RoundCylinderTangent ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q), s)) :=
    Module.Finite.of_basis b
  have hGram : Matrix.of (fun i j => inner ℝ (b i) (b j)) =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) := by
    ext i j
    simp only [Matrix.of_apply, b]
    rw [roundCylinderChartBasis_apply, roundCylinderChartBasis_apply]
    change roundCylinderProductMetric.inner _ _ _ = _
    exact roundCylinderChartFrame_gram q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) i j
  apply abs_multilinear_apply_le_of_inverse_gram_contraction_le
    (componentMultilinearMap
      (roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        N.normalized_pullback 1
          (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s)) b) b N.epsilon_pos.le
  have hnorm := N.normalized_pullback_first_derivative_normSquared_lt
    (z := ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q), s)) hs
  have hq : (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q) = q :=
    (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv
      (mem_chart_source _ q)
  rw [hq] at hnorm
  rw [hGram]
  simpa only [componentMultilinearMap_basis, roundCylinderTensorNormSquared,
    Matrix.of_apply, b, roundCylinderChartBasis_apply] using hnorm.le

end PoincareMT.EpsilonNeck
