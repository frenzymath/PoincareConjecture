import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderRegularity

/-!
# Exact comparison with the evolving round cylinder

The model has zero comparison error at every spatial derivative order. This
provides the metric-comparison field of a strong neck once its normalized
pullback has been identified with the evolving round cylinder.

Reference: Morgan--Tian, Definition 9.82 and Corollary 9.88, pp. 235--240.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT

/-- Every comparison derivative of the exact cylinder model vanishes. -/
theorem roundCylinderIteratedDerivative_model
    (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) :
    roundCylinderIteratedDerivative u c (EvolvingRoundCylinderMetric u) k = 0 := by
  induction k with
  | zero =>
      funext p a
      simp [roundCylinderIteratedDerivative, roundCylinderGram]
  | succ k ih =>
      rw [roundCylinderIteratedDerivative, ih]
      funext p a
      simp [roundCylinderTensorDerivative]

/-- The exact model has zero squared jet error, at any derivative order. -/
theorem roundCylinderJetErrorSquared_model
    (u : ℝ) (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u (EvolvingRoundCylinderMetric u) order z = 0 := by
  simp [roundCylinderJetErrorSquared, roundCylinderIteratedDerivative_model,
    roundCylinderTensorNormSquared]

/-- The model satisfies the frozen strong-neck comparison on any time set. -/
theorem roundCylinderFamilyClose_model {epsilon : ℝ} (hε : 0 < epsilon)
    (I : Set ℝ) :
    RoundCylinderFamilyClose epsilon I EvolvingRoundCylinderMetric := by
  refine ⟨?_, 0, sq_pos_of_pos hε, ?_⟩
  · intro u _ q a b
    exact (contDiff_roundCylinderGram u q a b).contDiffOn
  · intro u _ z _
    rw [roundCylinderJetErrorSquared_model]

/-- The terminal exact cylinder also satisfies the static neck comparison. -/
theorem roundCylinderClose_model {epsilon : ℝ} (hε : 0 < epsilon) (u : ℝ) :
    RoundCylinderClose epsilon u (EvolvingRoundCylinderMetric u) := by
  refine ⟨?_, 0, sq_pos_of_pos hε, ?_⟩
  · intro q a b
    exact (contDiff_roundCylinderGram u q a b).contDiffOn
  · intro z _
    rw [roundCylinderJetErrorSquared_model]

end PoincareMT
