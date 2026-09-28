import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder.Reflection.Tensors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderReflection

variable (B : RoundCylinderTwoTensor)
  (hB : ∀ (z : RoundCylinderSpace) (a b : ℝ) (v w : RoundCylinderTangent z),
    B z (a • v) (b • w) = a * b * B z v w)

include hB

theorem iteratedDerivative_pullback (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2))) :
    ∀ k : ℕ, roundCylinderIteratedDerivative u c (pullback B) k =
      tensor (roundCylinderIteratedDerivative u c B k)
  | 0 => by
    funext p a
    simp only [roundCylinderIteratedDerivative, tensor]
    rw [coefficient_pullback B hB, gram_parity u c p (a 0) (a 1)]
    simp only [weight, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
      Fin.succ_zero_eq_one]
    ring
  | k + 1 => by
    change roundCylinderTensorDerivative u c
      (roundCylinderIteratedDerivative u c (pullback B) k) =
      tensor (roundCylinderTensorDerivative u c (roundCylinderIteratedDerivative u c B k))
    rw [iteratedDerivative_pullback u c k]
    funext p a
    exact derivative_tensor u c (roundCylinderIteratedDerivative u c B k) p a

theorem jetErrorSquared_pullback (u : ℝ) (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u (pullback B) order z =
      roundCylinderJetErrorSquared u B order (space z) := by
  unfold roundCylinderJetErrorSquared
  dsimp only [space]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivative_pullback B hB]
  exact normSquared_tensor u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
    (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k)
    (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)

theorem smoothOn_pullback {epsilon : ℝ} (h : RoundCylinderTensorSmoothOn epsilon B) :
    RoundCylinderTensorSmoothOn epsilon (pullback B) := by
  intro q a b
  have hc : ContDiffOn ℝ ∞
      (fun p : RoundCylinderCoordinates => roundCylinderTensorCoefficient B
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (coordinates p) a b)
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
        Set.Ioo (-epsilon⁻¹) epsilon⁻¹) := by
    apply (h q a b).comp coordinates.contDiff.contDiffOn
    intro p hp
    refine ⟨hp.1, ?_⟩
    change -epsilon⁻¹ < -p.2 ∧ -p.2 < epsilon⁻¹
    rcases hp.2 with ⟨hl, hr⟩
    constructor <;> linarith
  have heq :
      (fun p : RoundCylinderCoordinates => roundCylinderTensorCoefficient (pullback B)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) =
      fun p => (sign a * sign b) * roundCylinderTensorCoefficient B
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (coordinates p) a b :=
    funext fun p => coefficient_pullback B hB _ p a b
  rw [heq]
  exact contDiffOn_const.mul hc

theorem close_pullback {epsilon u : ℝ} (h : RoundCylinderClose epsilon u B) :
    RoundCylinderClose epsilon u (pullback B) := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := h
  refine ⟨smoothOn_pullback B hB hsmooth, bound, hbound, ?_⟩
  intro z hz
  rw [jetErrorSquared_pullback B hB]
  apply hjet
  change -epsilon⁻¹ < -z.2 ∧ -z.2 < epsilon⁻¹
  rcases hz with ⟨hl, hr⟩
  constructor <;> linarith

end PoincareConjecture.RoundCylinderReflection
