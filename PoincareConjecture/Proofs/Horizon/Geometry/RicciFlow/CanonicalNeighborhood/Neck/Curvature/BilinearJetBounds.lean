import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped ContDiff

namespace PoincareConjecture


theorem norm_iteratedFDeriv_bilinear_le_nine_of_cylinder_components
    {F : EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (hF : ContDiffAt ℝ ∞ F x)
    (m : ℕ) {C : ℝ}
    (h : ∀ i j, ‖iteratedFDeriv ℝ m (fun y => F y
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ m F x‖ ≤ 9 * C := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).reindex ((finRotate 3).symm)
  have hb (i : Fin 3) : b i = roundCylinderEuclideanBasis i := by
    rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.reindex_toBasis]
    rfl
  have hh := SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components b hF m
    (fun i j => by simpa only [hb] using h i j)
  norm_num at hh ⊢
  exact hh

private theorem norm_iteratedFDeriv_two_sub
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F G : E → V) (x : E) :
    ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 G x‖ =
      ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x‖ := by
  simp only [← dist_eq_norm, iteratedFDeriv_succ_eq_comp_right,
    Function.comp_apply, LinearIsometryEquiv.dist_map, iteratedFDeriv_zero_eq_comp]


theorem cylinder_metric_twoJet_norm_sub_le
    {F G : EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hF : ContDiffAt ℝ ∞ F x) (hG : ContDiffAt ℝ ∞ G x) {C : ℝ}
    (h : ∀ m : ℕ, m ≤ 2 → ∀ i j,
      ‖iteratedFDeriv ℝ m (fun y =>
        F y (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        G y (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) x‖ ≤ C) :
    ‖F x - G x‖ ≤ 9 * C ∧
      ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤ 9 * C ∧
      ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x‖ ≤ 9 * C := by
  have hall (m : ℕ) (hm : m ≤ 2) : ‖iteratedFDeriv ℝ m (F - G) x‖ ≤ 9 * C :=
    norm_iteratedFDeriv_bilinear_le_nine_of_cylinder_components (hF.sub hG) m
      (fun i j => by simpa only [Pi.sub_apply, sub_apply] using h m hm i j)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hall 0 (by norm_num)
  · have h1 := hall 1 (by norm_num)
    rw [norm_iteratedFDeriv_one,
      fderiv_sub (hF.differentiableAt (by simp)) (hG.differentiableAt (by simp))] at h1
    exact h1
  · have h2 := hall 2 (by norm_num)
    have htwo : (2 : ℕ∞ω) ≤ ∞ := by decide
    rw [iteratedFDeriv_sub_apply (hF.of_le htwo) (hG.of_le htwo),
      norm_iteratedFDeriv_two_sub] at h2
    exact h2

end PoincareConjecture
