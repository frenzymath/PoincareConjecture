import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.RicciNormEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Kato
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace LeviCivitaData

variable {g : RiemannianMetric n M}

theorem ricciNormSq_pos_of_scalarCurvature_pos (D : LeviCivitaData g)
    {x : M} (hR : 0 < D.scalarCurvature x) : 0 < D.ricciNormSq x := by
  classical
  let b := g.orthonormalBasis x
  have htrace : (∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), (0 : ℝ)) <
      ∑ i, D.ricci x (b i) (b i) := by
    simpa only [Finset.sum_const_zero, scalarCurvature, b] using hR
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt htrace
  have hs : (D.ricci x (b i) (b i)) ^ 2 ≤ D.ricciNormSq x :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (D.ricci x (b i) (b j)))
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ =>
        sq_nonneg (D.ricci x (b j) (b k))) (Finset.mem_univ i))
  exact (sq_pos_of_pos hi).trans_le hs

theorem normalizedRicciNormSq_gradient_bound (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hR : ∀ y : M, 0 < D.scalarCurvature y)
    {x : M}
    (hcrit : D.gradient (fun y => D.ricciNormSq y / D.scalarCurvature y ^ 2) x = 0) :
    D.ricciNormSq x / D.scalarCurvature x ^ 2 *
        g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) ≤
      ∑ k, ∑ i, ∑ j,
        (D.covariantTensorDerivative D.ricciEvaluation x
          ![g.orthonormalBasis x k, g.orthonormalBasis x i, g.orthonormalBasis x j]) ^ 2 := by
  let q := fun y => D.ricciNormSq y / D.scalarCurvature y ^ 2
  have hRs := hD.contMDiff_scalarCurvature
  have hSs := RicciFlow.contMDiff_ricciNormSq D hD
  have hqs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q :=
    hSs.div₀ (hRs.pow 2) (fun y => pow_ne_zero _ (hR y).ne')
  have hprod : (fun y => q y * (D.scalarCurvature y * D.scalarCurvature y)) =
      D.ricciNormSq := by
    funext y
    simpa only [q, pow_two] using
      div_mul_cancel₀ (D.ricciNormSq y) (pow_ne_zero 2 (hR y).ne')
  have hgrad := D.gradient_mul ((hqs x).mdifferentiableAt (by simp))
    (((hRs x).mul (hRs x)).mdifferentiableAt (by simp))
  simp only [Pi.mul_apply, Pi.mul_def] at hgrad
  rw [hprod, D.gradient_mul ((hRs x).mdifferentiableAt (by simp))
    ((hRs x).mdifferentiableAt (by simp)), hcrit, smul_zero, add_zero] at hgrad
  have hnorm : g.inner x (D.gradient D.ricciNormSq x) (D.gradient D.ricciNormSq x) =
      (2 * q x * D.scalarCurvature x) ^ 2 *
        g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) := by
    rw [hgrad]
    simp only [smul_add, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hpair : g.tensorPairingTwo D.ricciEvaluation D.ricciEvaluation = D.ricciNormSq := by
    funext y
    simp only [RiemannianMetric.tensorPairingTwo, ricciNormSq, ricciEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one, pow_two]
  have hk := D.gradient_tensor_normSq_le hD.2.1 x
  dsimp only at hk
  rw [hpair, hnorm] at hk
  simp only [RiemannianMetric.tensorPairingThree, ← pow_two] at hk
  have hS := D.ricciNormSq_pos_of_scalarCurvature_pos (hR x)
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * D.ricciNormSq x from
    mul_pos (by norm_num) hS)).mp
  apply le_of_eq_of_le ?_ hk
  dsimp only [q]
  field_simp [(hR x).ne']
  ring

end LeviCivitaData

namespace RicciFlow

theorem normalizedRicciNormSq_deriv_le_at_localMax
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J)
    (hR : ∀ y : M, 0 < (F.connection t).scalarCurvature y) {x : M}
    (hmax : IsLocalMax (fun y =>
      (F.connection t).ricciNormSq y / (F.connection t).scalarCurvature y ^ 2) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    deriv (fun s => (F.connection s).ricciNormSq x /
      (F.connection s).scalarCurvature x ^ 2) t ≤
      4 * ((∑ i, ∑ j, D.ricci x (b i) (b j) *
        (∑ a, ∑ c, D.curvatureTensor x (b i) (b a) (b j) (b c) *
          D.ricci x (b a) (b c))) - D.ricciNormSq x ^ 2 / D.scalarCurvature x) /
        D.scalarCurvature x ^ 2 := by
  let D := F.connection t
  let q := fun y => D.ricciNormSq y / D.scalarCurvature y ^ 2
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hqs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q :=
    (contMDiff_ricciNormSq D hD).div₀ (hD.contMDiff_scalarCurvature.pow 2)
      (fun y => pow_ne_zero _ (hR y).ne')
  have hcrit : D.gradient q x = 0 := by
    simp only [LeviCivitaData.gradient,
      LeviCivitaData.mvfderiv_eq_zero_of_isLocalMax hqs hmax, map_zero]
  have hA := D.normalizedRicciNormSq_gradient_bound hD hR hcrit
  have hL := D.laplacian_nonpos_of_isLocalMax hqs hmax
  have heq := F.normalizedRicciNormSq_heat_equation hC ht hR x
  dsimp only at heq
  change D.gradient (fun y => D.ricciNormSq y / D.scalarCurvature y ^ 2) x = 0 at hcrit
  dsimp only [D] at hcrit
  rw [hcrit] at heq
  simp only [map_zero, zero_apply, mul_zero, add_zero] at heq
  have halg : 4 * (D.ricciNormSq x / D.scalarCurvature x ^ 2) *
      D.scalarCurvature x * D.ricciNormSq x =
        4 * D.ricciNormSq x ^ 2 / D.scalarCurvature x := by
    field_simp [(hR x).ne']
  rw [halg] at heq
  rw [heq]
  calc
    _ ≤ 0 + (4 * (∑ i, ∑ j, D.ricci x
        ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x j) *
        (∑ a, ∑ c, D.curvatureTensor x ((F.metric t).orthonormalBasis x i)
          ((F.metric t).orthonormalBasis x a) ((F.metric t).orthonormalBasis x j)
          ((F.metric t).orthonormalBasis x c) * D.ricci x
            ((F.metric t).orthonormalBasis x a) ((F.metric t).orthonormalBasis x c))) -
        4 * D.ricciNormSq x ^ 2 / D.scalarCurvature x) / D.scalarCurvature x ^ 2 := by
      apply add_le_add hL
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith only [hA]
    _ = _ := by ring

end RicciFlow

end PoincareConjecture
