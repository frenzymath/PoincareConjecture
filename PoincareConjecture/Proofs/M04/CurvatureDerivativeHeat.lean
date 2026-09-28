import PoincareConjecture.Proofs.M04.CurvaturePairingBounds
import PoincareConjecture.Proofs.M04.CurvatureDerivativeCorrection
import PoincareConjecture.Proofs.M04.CurvatureDerivativeReactionBounds
import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner
import PoincareConjecture.Proofs.M04.CurvatureEnergyTime

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem hasDerivAt_curvatureDerivativeEnergy
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    let D := F.connection t
    HasDerivAt
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm 1 x) ^ 2)
      (2 * (∑ a : Fin 5 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).riemannEvaluation 1 x
            (fun i ↦ (F.metric t).orthonormalBasis x (a i)) *
        ((F.connection t).tensorLaplacian
          ((F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).riemannEvaluation 1) x
            (fun i ↦ (F.metric t).orthonormalBasis x (a i)) +
          curvatureDerivativeReaction (F.connection t) 1 x
            (fun i ↦ (F.metric t).orthonormalBasis x (a i)))) +
        2 * (∑ j : Fin 5,
          ∑ a : Fin 5 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          ∑ l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
            (F.connection t).ricci x
              ((F.metric t).orthonormalBasis x (a j))
              ((F.metric t).orthonormalBasis x l) *
            (F.connection t).iteratedCovariantTensorDerivative
              (F.connection t).riemannEvaluation 1 x
              (fun i ↦ (F.metric t).orthonormalBasis x (a i)) *
            (F.connection t).iteratedCovariantTensorDerivative
              (F.connection t).riemannEvaluation 1 x
              (fun i ↦ (F.metric t).orthonormalBasis x
                (Function.update a j l i)))) t := by
  classical
  let D := F.connection t
  let T : ℝ → CovariantTensorEvaluation n M 5 :=
    fun s ↦ (F.connection s).iteratedCovariantTensorDerivative
      (F.connection s).riemannEvaluation 1
  let P : (Fin 5 → TangentSpace (𝓡 n) x) → ℝ := fun v ↦
    D.tensorLaplacian (D.iteratedCovariantTensorDerivative D.riemannEvaluation 1) x v +
      curvatureDerivativeReaction D 1 x v
  have hSmooth (s : ℝ) : IsSmoothCovariantTensor (T s) := by
    exact isSmoothCovariantTensor_covariantTensorDerivative (F.connection s)
      (isSmoothCovariantTensor_riemannEvaluation (F.connection s))
  have hTime (v : Fin 5 → TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s ↦ T s x v) (P v) t := by
    simpa only [T, P] using hasDerivAt_iteratedRiemann_evolution F 1 ht x v
  have h := hasDerivAt_flow_tensorNorm_sq F T hSmooth ht x P hTime
  change HasDerivAt (fun s ↦ ((F.connection s).curvatureDerivativeNorm 1 x) ^ 2) _ t at h
  simpa only [T, D, P, LeviCivitaData.tensorLaplacian,
    LeviCivitaData.curvatureDerivativeNorm, Fin.cons_zero, Fin.cons_succ] using h

theorem curvatureDerivative_reaction_pair_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) :
    tensorPairing g
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation 1)
        (curvatureDerivativeReaction D 1) x ≤
      98 * (n : ℝ) * D.curvatureDerivativeNorm 0 x *
        (D.curvatureDerivativeNorm 1 x) ^ 2 := by
  classical
  let N0 := D.curvatureDerivativeNorm 0 x
  let N1 := D.curvatureDerivativeNorm 1 x
  have hN1 : 0 ≤ N1 := Real.sqrt_nonneg _
  have hPair := abs_tensorPairing_le_tensorNorm_mul (g := g)
    (D.iteratedCovariantTensorDerivative D.riemannEvaluation 1)
    (curvatureDerivativeReaction D 1) x
  have hTnorm : g.tensorNorm
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation 1) x = N1 := by
    change D.curvatureDerivativeNorm 1 x = N1
    rfl
  rw [hTnorm] at hPair
  have hReact := tensorNorm_curvatureDerivativeReaction_le D 1 x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hsum : (∑ i ∈ Finset.range (1 + 1),
      D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (1 - i) x) =
      N0 * N1 + N1 * N0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.zero_add, Nat.sub_zero, Nat.sub_self, Nat.cast_one]
    ring
  have hbound : N1 *
      ((Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        (curvatureReactionWeight 1 : ℝ) *
        (∑ i ∈ Finset.range (1 + 1),
          D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (1 - i) x)) ≤
      98 * (n : ℝ) * N0 * N1 ^ 2 := by
    rw [hsum]
    simp only [curvatureReactionWeight, hdim]
    apply le_of_eq
    ring
  calc
    tensorPairing g
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation 1)
        (curvatureDerivativeReaction D 1) x ≤
      |tensorPairing g
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation 1)
        (curvatureDerivativeReaction D 1) x| := le_abs_self _
    _ ≤ N1 * g.tensorNorm (curvatureDerivativeReaction D 1) x := by
      simpa only [LeviCivitaData.curvatureDerivativeNorm] using hPair
    _ ≤ _ := (mul_le_mul_of_nonneg_left hReact hN1).trans hbound

theorem curvatureDerivative_heat_inequality_interior_of_correction
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M)
    {C : ℝ}
    (hCorrection :
      2 * (∑ j : Fin 5,
        ∑ a : Fin 5 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          (F.connection t).ricci x
            ((F.metric t).orthonormalBasis x (a j))
            ((F.metric t).orthonormalBasis x l) *
          (F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).riemannEvaluation 1 x
            (fun i ↦ (F.metric t).orthonormalBasis x (a i)) *
          (F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).riemannEvaluation 1 x
            (fun i ↦ (F.metric t).orthonormalBasis x
              (Function.update a j l i))) ≤
      C * (F.connection t).curvatureDerivativeNorm 0 x *
        ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2) :
    derivWithin
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm 1 x) ^ 2) J t ≤
      (F.connection t).laplacian
        (fun y ↦ ((F.connection t).curvatureDerivativeNorm 1 y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm 2 x) ^ 2 +
      (196 * (n : ℝ) + C) *
        (F.connection t).curvatureDerivativeNorm 0 x *
          ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 := by
  classical
  let D := F.connection t
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hderiv := (hasDerivAt_curvatureDerivativeEnergy F ht x).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_convex hconv hne t (interior_subset ht))
  have hbochner := laplacian_tensorNorm_sq D
    (isSmoothCovariantTensor_covariantTensorDerivative D
      (isSmoothCovariantTensor_riemannEvaluation D)) x
  change D.laplacian (fun y ↦ (D.curvatureDerivativeNorm 1 y) ^ 2) x = _ at hbochner
  change D.laplacian (fun y ↦ (D.curvatureDerivativeNorm 1 y) ^ 2) x =
    2 * tensorPairing (F.metric t)
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation 1)
        (D.tensorLaplacian (D.iteratedCovariantTensorDerivative
          D.riemannEvaluation 1)) x +
      2 * (D.curvatureDerivativeNorm 2 x) ^ 2 at hbochner
  simp only [tensorPairing] at hbochner
  simp only [mul_add, Finset.sum_add_distrib] at hderiv
  have hpair := curvatureDerivative_reaction_pair_le (g := F.metric t) D x
  simp only [tensorPairing] at hpair
  dsimp only [D] at hderiv hbochner hpair hCorrection ⊢
  linarith

theorem curvatureDerivative_heat_inequality_interior
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    derivWithin
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm 1 x) ^ 2) J t ≤
      (F.connection t).laplacian
        (fun y ↦ ((F.connection t).curvatureDerivativeNorm 1 y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm 2 x) ^ 2 +
      (196 * (n : ℝ) + 10 * (n : ℝ) ^ 7) *
        (F.connection t).curvatureDerivativeNorm 0 x *
          ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 := by
  apply curvatureDerivative_heat_inequality_interior_of_correction F ht x
  simpa only [mul_assoc] using
    (inverse_metric_correction_le (g := F.metric t) (F.connection t) x)

end PoincareConjecture.M04
