import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.DefectTestCoefficient
import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n r : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem tensorNorm_sq_fixed_coefficients (g : RiemannianMetric n V)
    (H : V → (Fin r → V) → ℝ) (hH : IsSmoothCovariantTensor H) (x : V) :
    (g.tensorNorm H x) ^ 2 =
      ∑ a : Fin r → Fin n, ∑ b : Fin r → Fin n,
        H x (fun j => e (a j)) * H x (fun j => e (b j)) *
          ∏ j : Fin r, g.inverseCoefficients x (a j) (b j) := by
  let E : V ≃L[ℝ] TangentSpace (𝓡 n) x := ContinuousLinearEquiv.refl ℝ V
  have hE (v : V) : E v = v := rfl
  have hEs (v : V) : E.symm v = v := rfl
  have he (i j : Fin n) : M04.frameInverseGram g x E.toContinuousLinearMap i j =
      g.inverseCoefficients x i j := by
    rw [← M04.frameInverseGram_eq_coordinate_sum, inverseCoefficients_eq_orthonormal_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hEs, EuclideanSpace.basisFun_inner, PiLp.proj_apply]
  have h := M04.tensorNorm_sq_eq_inverseGram g H x (hH.1 x) E
  simpa only [he, hE] using h

theorem raw_tensorNorm_sq_continuousOn {J I : Set ℝ} (F : RicciFlow n V J)
    (hIJ : I ⊆ J) {E : Set V} (H : ℝ → V → (Fin r → V) → ℝ)
    (hH : ∀ t, IsSmoothCovariantTensor (H t))
    (hcomponents : ∀ a : Fin r → Fin n,
      ContinuousOn (fun p : ℝ × V => H p.1 p.2 (fun j => e (a j))) (I ×ˢ E)) :
    ContinuousOn (fun p : ℝ × V => ((F.metric p.1).tensorNorm (H p.1) p.2) ^ 2)
      (I ×ˢ E) := by
  simp only [tensorNorm_sq_fixed_coefficients _ _ (hH _)]
  apply continuousOn_finsetSum
  intro a _
  apply continuousOn_finsetSum
  intro b _
  apply ((hcomponents a).mul (hcomponents b)).mul
  apply continuousOn_finsetProd
  intro j _
  exact ((raw_inverseCoefficients_family_contDiffOn F (a j) (b j)).continuousOn).mono
    (prod_mono hIJ (subset_univ E))

end PoincareConjecture.M35.Uniqueness.Heat
