import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseMetric
import PoincareConjecture.Proofs.M13.CurvatureContractions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem cap_scalar_frameInverseGram
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x) :
    let b0 := EuclideanSpace.basisFun (Fin n) ℝ
    D.scalarCurvature x = ∑ i, ∑ j,
      M04.frameInverseGram g x e.toContinuousLinearMap i j *
        D.ricci x (e (b0 i)) (e (b0 j)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let b := g.orthonormalBasis x
  let c (i : Fin n) (v : TangentSpace (𝓡 n) x) := inner ℝ (b0 i) (e.symm v)
  have hrec (v : TangentSpace (𝓡 n) x) : (∑ i, c i v • e (b0 i)) = v := by
    calc
      _ = e (∑ i, c i v • b0 i) := by simp only [map_sum, map_smul]
      _ = e (e.symm v) := congrArg e (b0.sum_repr' (e.symm v))
      _ = v := e.apply_symm_apply v
  have hpair (v : TangentSpace (𝓡 n) x) :
      D.ricci x v v = ∑ i, ∑ j, c i v * c j v * D.ricci x (e (b0 i)) (e (b0 j)) := by
    rw [← M13.ricciLinear_apply D x]
    conv_lhs => rw [← hrec v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [M13.ricciLinear_apply, M04.ricci_symm D x (e (b0 j)) (e (b0 i))]
    ring
  change D.scalarCurvature x = _
  calc
    _ = ∑ a, D.ricci x (b a) (b a) := rfl
    _ = ∑ a, ∑ i, ∑ j, c i (b a) * c j (b a) *
        D.ricci x (e (b0 i)) (e (b0 j)) := Finset.sum_congr rfl (fun a _ => hpair (b a))
    _ = ∑ i, ∑ j, (∑ a, c i (b a) * c j (b a)) *
        D.ricci x (e (b0 i)) (e (b0 j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact (Finset.sum_mul _ _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact M04.frameInverseGram_eq_coordinate_sum g x e i j

theorem cap_scalar_difference_frame
    {g0 g1 : RiemannianMetric n M} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (x : M) (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x) :
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    let A0 := M04.frameInverseGram g0 x e.toContinuousLinearMap
    let A1 := M04.frameInverseGram g1 x e.toContinuousLinearMap
    D1.scalarCurvature x - D0.scalarCurvature x =
      (∑ i, ∑ j, (A1 i j - A0 i j) * D0.ricci x (e (b i)) (e (b j))) +
      ∑ i, ∑ j, A1 i j * (D1.ricci x (e (b i)) (e (b j)) -
        D0.ricci x (e (b i)) (e (b j))) := by
  dsimp only
  rw [cap_scalar_frameInverseGram D1 x e, cap_scalar_frameInverseGram D0 x e]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end PoincareConjecture.M47
