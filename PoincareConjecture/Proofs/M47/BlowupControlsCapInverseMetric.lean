import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy
import PoincareConjecture.Proofs.M04.ConnectionDifference

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem cap_frameGram_inner (g : RiemannianMetric n M) (x : M)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) x)
    (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (M04.frameGramOperator g x L v) w = g.inner x (L v) (L w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (((g.inner x).bilinearComp L L) v)) w = _
  exact InnerProductSpace.toDual_symm_apply

theorem cap_frameInverseGram_coordinate (g : RiemannianMetric n M) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (V : TangentSpace (𝓡 n) x) (i : Fin n) :
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    inner ℝ (b i) (e.symm V) =
      ∑ j, M04.frameInverseGram g x e.toContinuousLinearMap i j *
        g.inner x V (e (b j)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let A := M04.frameGramOperator g x e.toContinuousLinearMap
  have hinv : A.IsInvertible := M04.frameGramOperator_isInvertible g x e
  have hexpand : (∑ j, g.inner x V (e (b j)) • b j) = A (e.symm V) := by
    conv_rhs => rw [← b.sum_repr (A (e.symm V))]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [b.repr_apply_apply, real_inner_comm]
    change _ = inner ℝ (M04.frameGramOperator g x e.toContinuousLinearMap (e.symm V))
      (b j)
    rw [cap_frameGram_inner]
    simp only [ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
  change inner ℝ (b i) (e.symm V) = _
  calc
    _ = inner ℝ (b i) (A.inverse (A (e.symm V))) := by rw [hinv.inverse_apply_self]
    _ = _ := by
      rw [← hexpand, map_sum, inner_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [map_smul, inner_smul_right]
      change g.inner x V (e (b j)) * M04.frameInverseGram g x e.toContinuousLinearMap i j = _
      ring

theorem cap_frameInverseGram_norm_le (g : RiemannianMetric n M) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    {gamma : ℝ} (hgamma : gamma < 1)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),
      (1 - gamma) * ‖v‖ ^ 2 ≤ g.inner x (e v) (e v)) :
    ‖(M04.frameGramOperator g x e.toContinuousLinearMap).inverse‖ ≤
      (1 - gamma)⁻¹ := by
  let A := M04.frameGramOperator g x e.toContinuousLinearMap
  have hinv : A.IsInvertible := M04.frameGramOperator_isInvertible g x e
  have hpos : 0 < 1 - gamma := sub_pos.mpr hgamma
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hpos.le)
  intro v
  have hquad := hlower (A.inverse v)
  have hpair := cap_frameGram_inner g x e.toContinuousLinearMap (A.inverse v) (A.inverse v)
  change inner ℝ (A (A.inverse v)) (A.inverse v) = _ at hpair
  rw [hinv.self_apply_inverse] at hpair
  change inner ℝ v (A.inverse v) = g.inner x (e (A.inverse v)) (e (A.inverse v)) at hpair
  have hinner := real_inner_le_norm v (A.inverse v)
  by_cases hz : ‖A.inverse v‖ = 0
  · change ‖A.inverse v‖ ≤ _
    rw [hz]
    positivity
  · have hn : 0 < ‖A.inverse v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hmul : (1 - gamma) * ‖A.inverse v‖ ≤ ‖v‖ := by
      apply le_of_mul_le_mul_right _ hn
      calc
        (1 - gamma) * ‖A.inverse v‖ * ‖A.inverse v‖ =
            (1 - gamma) * ‖A.inverse v‖ ^ 2 := by ring
        _ ≤ g.inner x (e (A.inverse v)) (e (A.inverse v)) := hquad
        _ = inner ℝ v (A.inverse v) := hpair.symm
        _ ≤ ‖v‖ * ‖A.inverse v‖ := hinner
    change ‖A.inverse v‖ ≤ (1 - gamma)⁻¹ * ‖v‖
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hpos).mpr (by nlinarith only [hmul])

theorem cap_frameInverseGram_sub_identity (g : RiemannianMetric n M) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x) :
    let A := M04.frameGramOperator g x e.toContinuousLinearMap
    A.inverse - ContinuousLinearMap.id ℝ _ =
      -(A.inverse.comp (A - ContinuousLinearMap.id ℝ _)) := by
  let A := M04.frameGramOperator g x e.toContinuousLinearMap
  have hinv : A.IsInvertible := M04.frameGramOperator_isInvertible g x e
  apply ContinuousLinearMap.ext
  intro v
  change A.inverse v - v = -(A.inverse (A v - v))
  rw [map_sub, hinv.inverse_apply_self]
  abel

set_option backward.isDefEq.respectTransparency false in

theorem cap_connection_difference_components
    {g0 g1 : RiemannianMetric n M} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    {x : M} (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (Z : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : ∀ j, MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (Z j)) x)
    (hZx : ∀ j, Z j x = e (EuclideanSpace.basisFun (Fin n) ℝ j)) (i : Fin n) :
    let H : CovariantTensorEvaluation n M 2 :=
      fun y v ↦ g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
    inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
      (e.symm (D1.connection Y x (X x) - D0.connection Y x (X x))) =
      (1 / 2 : ℝ) * ∑ j, M04.frameInverseGram g1 x e.toContinuousLinearMap i j *
        (M04.covariantTensorDerivativeOnFields D0 H ![X, Y, Z j] x +
          M04.covariantTensorDerivativeOnFields D0 H ![Y, X, Z j] x -
          M04.covariantTensorDerivativeOnFields D0 H ![Z j, X, Y] x) := by
  dsimp only
  rw [cap_frameInverseGram_coordinate g1 x e _ i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hpair := M04.connection_difference_pairing D0 D1 hX hY (hZ j)
  dsimp only at hpair
  rw [hZx j] at hpair
  rw [← hpair]
  ring

end PoincareConjecture.M47
