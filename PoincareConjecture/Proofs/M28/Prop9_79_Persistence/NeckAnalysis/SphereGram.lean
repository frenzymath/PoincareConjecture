import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem sphere_chart_center (q : UnitTwoSphere) :
    chartAt (EuclideanSpace ℝ (Fin 2)) q q = 0 := by
  change stereographic' 2 (-q) q = 0
  dsimp [stereographic']
  simp only [EmbeddingLike.map_eq_zero_iff]
  exact stereographic_neg_apply q

theorem sphere_chart_inverse_inner (q : UnitTwoSphere)
    (v w : EuclideanSpace ℝ (Fin 2)) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) (c.symm (c q))
        (mfderiv (𝓡 2) (𝓡 2) c.symm (c q) v))
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) (c.symm (c q))
        (mfderiv (𝓡 2) (𝓡 2) c.symm (c q) w)) = inner ℝ v w := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere (-q))).repr
  have hc : c q = 0 := sphere_chart_center q
  have hderiv : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin 2) => (c.symm x).1)
      ((ℝ ∙ (↑(-q) : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.comp
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap) 0 := by
    have h := hasFDerivAt_stereoInvFunAux_comp_coe
      (↑(-q) : EuclideanSpace ℝ (Fin 3))
    have hzero : U.symm 0 = 0 := map_zero _
    rw [← hzero] at h
    exact h.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt
  have htarget : c q ∈ c.target := c.map_source (mem_chart_source _ q)
  have hsymm : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm (c q) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ q) htarget
  have hcoe : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun x : UnitTwoSphere => x.1) (c.symm (c q)) :=
    (contMDiff_coe_sphere (c.symm (c q))).mdifferentiableAt one_ne_zero
  have hcomp :
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) (c.symm (c q))).comp
        (mfderiv (𝓡 2) (𝓡 2) c.symm (c q)) =
      (ℝ ∙ (↑(-q) : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.comp
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [← mfderiv_comp (c q) hcoe hsymm, mfderiv_eq_fderiv, hc]
    exact hderiv.fderiv
  change inner ℝ
    (((mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) (c.symm (c q))).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm (c q))) v)
    (((mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) (c.symm (c q))).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm (c q))) w) = _
  rw [hcomp]
  exact U.symm.inner_map_map v w

def cylinderGramDiagonal (u : ℝ) : Fin 3 → ℝ :=
  ![2 * (1 - u), 2 * (1 - u), 1]

theorem roundCylinderGram_chosen_center (u : ℝ) (z : RoundCylinderSpace) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) =
      Matrix.diagonal (cylinderGramDiagonal u) := by
  ext a b
  dsimp [roundCylinderGram, roundCylinderTensorCoefficient, EvolvingRoundCylinderMetric]
  rw [sphere_chart_inverse_inner]
  fin_cases a <;> fin_cases b <;>
    simp [roundCylinderCoordinateBasis, cylinderGramDiagonal, Matrix.diagonal,
      EuclideanSpace.inner_single_left]

theorem cylinderGramDiagonal_pos {u : ℝ} (hu : u < 1) (a : Fin 3) :
    0 < cylinderGramDiagonal u a := by
  fin_cases a <;> simp [cylinderGramDiagonal] <;> linarith

theorem roundCylinderGram_inverse_chosen_center {u : ℝ} (hu : u < 1)
    (z : RoundCylinderSpace) :
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2))⁻¹ =
      Matrix.diagonal (fun a => (cylinderGramDiagonal u a)⁻¹) := by
  rw [roundCylinderGram_chosen_center]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst b
    simp [Matrix.diagonal, ne_of_gt (cylinderGramDiagonal_pos hu a)]
  · simp [Matrix.diagonal, hab]

end PoincareConjecture.Proofs.M28.NeckAnalysis
