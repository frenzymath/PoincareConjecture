import PoincareConjecture.Proofs.M04.CurvaturePairingBounds
import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner
import PoincareConjecture.Proofs.M04.CurvatureEnergyTime
import PoincareConjecture.Proofs.M04.CurvatureDerivativeEvolution
import PoincareConjecture.Proofs.M04.CurvatureDerivativeReactionBounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem isSmooth_iteratedRiemann {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (m : ℕ) :
    IsSmoothCovariantTensor
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) := by
  induction m with
  | zero => exact isSmoothCovariantTensor_riemannEvaluation D
  | succ m ih =>
    exact isSmoothCovariantTensor_covariantTensorDerivative D ih

private theorem hasDerivAt_curvatureDerivativeEnergy_general
    (F : RicciFlow n M J) (m : ℕ) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    let D := F.connection t
    HasDerivAt
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm m x) ^ 2)
      (2 * (∑ a : Fin (4 + m) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).riemannEvaluation m x
            (fun i ↦ (F.metric t).orthonormalBasis x (a i)) *
        ((F.connection t).tensorLaplacian
          ((F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).riemannEvaluation m) x
            (fun i ↦ (F.metric t).orthonormalBasis x (a i)) +
          curvatureDerivativeReaction (F.connection t) m x
            (fun i ↦ (F.metric t).orthonormalBasis x (a i)))) +
        2 * (∑ j : Fin (4 + m),
          ∑ a : Fin (4 + m) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          ∑ l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
            (F.connection t).ricci x
              ((F.metric t).orthonormalBasis x (a j))
              ((F.metric t).orthonormalBasis x l) *
            (F.connection t).iteratedCovariantTensorDerivative
              (F.connection t).riemannEvaluation m x
              (fun i ↦ (F.metric t).orthonormalBasis x (a i)) *
            (F.connection t).iteratedCovariantTensorDerivative
              (F.connection t).riemannEvaluation m x
              (fun i ↦ (F.metric t).orthonormalBasis x
                (Function.update a j l i)))) t := by
  classical
  let D := F.connection t
  let T : ℝ → CovariantTensorEvaluation n M (4 + m) :=
    fun s ↦ (F.connection s).iteratedCovariantTensorDerivative
      (F.connection s).riemannEvaluation m
  let P : (Fin (4 + m) → TangentSpace (𝓡 n) x) → ℝ := fun v ↦
    D.tensorLaplacian (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) x v +
      curvatureDerivativeReaction D m x v
  have hSmooth (s : ℝ) : IsSmoothCovariantTensor (T s) := by
    exact isSmooth_iteratedRiemann (F.connection s) m
  have hTime (v : Fin (4 + m) → TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s ↦ T s x v) (P v) t := by
    simpa only [T, P] using hasDerivAt_iteratedRiemann_evolution F m ht x v
  have h := hasDerivAt_flow_tensorNorm_sq F T hSmooth ht x P hTime
  change HasDerivAt (fun s ↦ ((F.connection s).curvatureDerivativeNorm m x) ^ 2) _ t at h
  simpa only [T, D, P, LeviCivitaData.tensorLaplacian,
    LeviCivitaData.curvatureDerivativeNorm, Fin.cons_zero, Fin.cons_succ] using h

theorem curvatureDerivative_reaction_pair_le_general
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (m : ℕ) (x : M) :
    tensorPairing g
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation m)
        (curvatureDerivativeReaction D m) x ≤
      D.curvatureDerivativeNorm m x *
        ((Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
          (curvatureReactionWeight m : ℝ) *
          (∑ i ∈ Finset.range (m + 1),
            D.curvatureDerivativeNorm i x *
              D.curvatureDerivativeNorm (m - i) x)) := by
  classical
  let Nm := D.curvatureDerivativeNorm m x
  have hNm : 0 ≤ Nm := by
    dsimp [Nm, LeviCivitaData.curvatureDerivativeNorm, RiemannianMetric.tensorNorm]
    exact Real.sqrt_nonneg _
  have hPair := abs_tensorPairing_le_tensorNorm_mul (g := g)
    (D.iteratedCovariantTensorDerivative D.riemannEvaluation m)
    (curvatureDerivativeReaction D m) x
  have hTnorm : g.tensorNorm
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) x = Nm := by
    change D.curvatureDerivativeNorm m x = Nm
    rfl
  rw [hTnorm] at hPair
  have hReact := tensorNorm_curvatureDerivativeReaction_le D m x
  calc
    tensorPairing g
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation m)
        (curvatureDerivativeReaction D m) x ≤
      |tensorPairing g
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation m)
        (curvatureDerivativeReaction D m) x| := le_abs_self _
    _ ≤ Nm * g.tensorNorm (curvatureDerivativeReaction D m) x := by
      simpa only [LeviCivitaData.curvatureDerivativeNorm] using hPair
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left hReact hNm

theorem curvatureDerivative_heat_inequality_interior_of_correction_general
    (F : RicciFlow n M J) (m : ℕ) {t : ℝ} (ht : t ∈ interior J) (x : M)
    {C : ℝ}
    (hCorrection :
      2 * (∑ j : Fin (4 + m),
        ∑ a : Fin (4 + m) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          (F.connection t).ricci x
            ((F.metric t).orthonormalBasis x (a j))
            ((F.metric t).orthonormalBasis x l) *
          (F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).riemannEvaluation m x
            (fun i ↦ (F.metric t).orthonormalBasis x (a i)) *
          (F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).riemannEvaluation m x
            (fun i ↦ (F.metric t).orthonormalBasis x
              (Function.update a j l i))) ≤
      C * (F.connection t).curvatureDerivativeNorm 0 x *
        ((F.connection t).curvatureDerivativeNorm m x) ^ 2) :
    derivWithin
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm m x) ^ 2) J t ≤
      (F.connection t).laplacian
        (fun y ↦ ((F.connection t).curvatureDerivativeNorm m y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm (m + 1) x) ^ 2 +
      2 * (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        (curvatureReactionWeight m : ℝ) *
        (F.connection t).curvatureDerivativeNorm m x *
          (∑ i ∈ Finset.range (m + 1),
            (F.connection t).curvatureDerivativeNorm i x *
            (F.connection t).curvatureDerivativeNorm (m - i) x) +
      C * (F.connection t).curvatureDerivativeNorm 0 x *
        ((F.connection t).curvatureDerivativeNorm m x) ^ 2 := by
  classical
  let D := F.connection t
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hderiv :=
    (hasDerivAt_curvatureDerivativeEnergy_general F m ht x).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_convex hconv hne t (interior_subset ht))
  have hTensor : IsSmoothCovariantTensor
      (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) :=
    isSmooth_iteratedRiemann D m
  have hbochner := laplacian_tensorNorm_sq D hTensor x
  change D.laplacian (fun y ↦ (D.curvatureDerivativeNorm m y) ^ 2) x = _ at hbochner
  change D.laplacian (fun y ↦ (D.curvatureDerivativeNorm m y) ^ 2) x =
    2 * tensorPairing (F.metric t)
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation m)
        (D.tensorLaplacian (D.iteratedCovariantTensorDerivative
          D.riemannEvaluation m)) x +
      2 * (D.curvatureDerivativeNorm (m + 1) x) ^ 2 at hbochner
  simp only [tensorPairing] at hbochner
  simp only [mul_add, Finset.sum_add_distrib] at hderiv
  have hpair := curvatureDerivative_reaction_pair_le_general D m x
  simp only [tensorPairing] at hpair
  dsimp only [D] at hderiv hbochner hpair hCorrection ⊢
  linarith

end PoincareConjecture.M04
