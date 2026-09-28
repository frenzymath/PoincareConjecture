import PoincareConjecture.Proofs.M47.TerminalCurvatureNeckSphere
import PoincareConjecture.Proofs.M36.NeckCurvatureJet
import PoincareConjecture.Proofs.M01.NormalizationCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M36 SpacetimeBounds



theorem exists_terminalCurvature_neck_positive_plane :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (N : EpsilonNeck g),
        N.epsilon ≤ delta → ∀ theta : UnitTwoSphere,
          ∃ a b : TangentSpace (𝓡 2) theta,
            0 < D.curvatureTensor (N.coordinate_map (theta, 0))
              (mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta a)
              (mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta b)
              (mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta a)
              (mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta b) := by
  obtain ⟨delta0, hdelta0, K, hK, hbound⟩ :=
    exists_normalizedNeck_curvature_component_bounds.{u}
  let delta := min delta0 (min (1 / 2) (1 / (2 * K)))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta, hdelta, ?_⟩
  intro M _ _ _ g D N hsmall theta
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have horder : 2 ≤ ⌊N.epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    change (2 : ℝ) ≤ N.epsilon⁻¹
    rw [← one_div, le_div_iff₀ N.epsilon_pos]
    linarith [N.epsilon_lt_half]
  have herr := hbound N (hsmall.trans (min_le_left _ _)) horder theta 0 hzero 0 1 0 1
  let e0 := EuclideanSpace.basisFun (Fin 3) ℝ 0
  let e1 := EuclideanSpace.basisFun (Fin 3) ℝ 1
  have hmodel : jetCurvature cylinderModelJet e0 e1 e0 e1 = 2 := by
    dsimp only [e0, e1]
    simp only [jetCurvature_cylinderModelJet, cylinderHorizontalForm_basis]
    norm_num [cylinderHorizontalGram, roundCylinderCoordinateBasis,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]
  have hsmallK : K * N.epsilon ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp
      (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hh]
  rw [hmodel] at herr
  have hpos : 0 < (normalizedNeckConnection N).curvatureTensor
      (centeredNeckLift N theta 0 0)
      (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e0)
      (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e1)
      (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e0)
      (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e1) := by
    have hlo := (abs_le.mp herr).1
    linarith only [hlo, hsmallK]
  rw [normalizedNeckConnection, m01RescaledMetric_curvatureTensor] at hpos
  have hneck := (mul_pos_iff_of_pos_left N.scalar_center_pos).mp hpos
  have heq := D.curvatureTensor_eq_of_local_isometry N.connection (f := id)
    isOpen_univ contMDiff_id.contMDiffOn
    (fun x _ v w => by simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply])
    (mem_univ (centeredNeckLift N theta 0 0))
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e0)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e1)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e0)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e1)
  simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] at heq
  have hactual := heq.symm ▸ hneck
  have he0 : cylinderHeightCovector e0 = 0 := by
    dsimp only [e0]
    rw [cylinderHeightCovector_basis]
    rfl
  have he1 : cylinderHeightCovector e1 = 0 := by
    dsimp only [e1]
    rw [cylinderHeightCovector_basis]
    rfl
  refine ⟨mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) theta).symm 0
      (cylinderHorizontalProjection e0),
    mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) theta).symm 0
      (cylinderHorizontalProjection e1), ?_⟩
  rw [terminalCurvature_neck_sphere_horizontal N theta e0 he0,
    terminalCurvature_neck_sphere_horizontal N theta e1 he1]
  let v0 : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e0
  let v1 : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e1
  have hpoint := congrArg (fun x : M => D.curvatureTensor x v0 v1 v0 v1)
    (centeredNeckLift_zero N theta 0)
  exact hpoint ▸ hactual

end PoincareConjecture.M47
