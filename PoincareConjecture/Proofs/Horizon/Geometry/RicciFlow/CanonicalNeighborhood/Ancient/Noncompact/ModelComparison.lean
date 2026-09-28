import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderRegularity











set_option autoImplicit false

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture


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


theorem roundCylinderJetErrorSquared_model
    (u : ℝ) (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u (EvolvingRoundCylinderMetric u) order z = 0 := by
  simp [roundCylinderJetErrorSquared, roundCylinderIteratedDerivative_model,
    roundCylinderTensorNormSquared]


theorem roundCylinderFamilyClose_model {epsilon : ℝ} (hε : 0 < epsilon)
    (I : Set ℝ) :
    RoundCylinderFamilyClose epsilon I EvolvingRoundCylinderMetric := by
  refine ⟨?_, 0, sq_pos_of_pos hε, ?_⟩
  · intro u _ q a b
    exact (contDiff_roundCylinderGram u q a b).contDiffOn
  · intro u _ z _
    rw [roundCylinderJetErrorSquared_model]


theorem roundCylinderClose_model {epsilon : ℝ} (hε : 0 < epsilon) (u : ℝ) :
    RoundCylinderClose epsilon u (EvolvingRoundCylinderMetric u) := by
  refine ⟨?_, 0, sq_pos_of_pos hε, ?_⟩
  · intro q a b
    exact (contDiff_roundCylinderGram u q a b).contDiffOn
  · intro z _
    rw [roundCylinderJetErrorSquared_model]

end PoincareConjecture
