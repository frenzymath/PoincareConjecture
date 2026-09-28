import PoincareConjecture.Definitions.Ch12.StandardCap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M38



theorem exists_positive_isometry (x y : StandardCapSpace) (h : ‖x‖ = ‖y‖) :
    ∃ e : StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace,
      LinearMap.det e.toLinearMap = 1 ∧ e x = y := by
  classical
  by_cases hxy : x = y
  · exact ⟨LinearIsometryEquiv.refl ℝ _, by simp, hxy⟩
  have hy : y ≠ 0 := by
    intro hy
    have hx : x = 0 := norm_eq_zero.mp (by simpa [hy] using h)
    exact hxy (hx.trans hy.symm)
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp⟩
  have hdim : Module.finrank ℝ (ℝ ∙ y)ᗮ = 2 :=
    Submodule.finrank_orthogonal_span_singleton hy
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero
    (R := ℝ) (M := (ℝ ∙ y)ᗮ)).mp (by omega)
  have hv0 : (v : StandardCapSpace) ≠ 0 := fun heq => hv (Subtype.ext heq)
  let a := (ℝ ∙ (x - y))ᗮ.reflection
  let b := (ℝ ∙ (v : StandardCapSpace))ᗮ.reflection
  have ha : a x = y := Submodule.reflection_sub h
  have hb : b y = y := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.2))
  have hda : LinearMap.det a.toLinearMap = -1 := by
    dsimp [a]
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton (sub_ne_zero.mpr hxy)]
    norm_num
  have hdb : LinearMap.det b.toLinearMap = -1 := by
    dsimp [b]
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton hv0]
    norm_num
  refine ⟨a.trans b, ?_, ?_⟩
  · change LinearMap.det (b.toLinearMap.comp a.toLinearMap) = 1
    rw [LinearMap.det_comp, hda, hdb]
    norm_num
  · change b (a x) = y
    rw [ha, hb]



theorem standardRotation_eq_toEuclideanLin
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    standardRotation A = A.1.toEuclideanLin := rfl



theorem exists_standardRotation (x y : StandardCapSpace) (h : ‖x‖ = ‖y‖) :
    ∃ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, standardRotation A x = y := by
  obtain ⟨e, hdet, he⟩ := exists_positive_isometry x y h
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let A := LinearMap.toMatrix b.toBasis b.toBasis e.toLinearMap
  have hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    apply Matrix.mem_specialOrthogonalGroup_iff.mpr
    exact ⟨e.toMatrix_mem_unitaryGroup b b, (LinearMap.det_toMatrix _ _).trans hdet⟩
  refine ⟨⟨A, hA⟩, ?_⟩
  rw [standardRotation_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  change Matrix.toLin b.toBasis b.toBasis
    (LinearMap.toMatrix b.toBasis b.toBasis e.toLinearMap) x = y
  rw [Matrix.toLin_toMatrix]
  exact he

end PoincareConjecture.M38
