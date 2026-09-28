import PoincareConjecture.Definitions.Ch01.ScalarOperators
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace









set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem preferredField_eq_inverseChartDerivative (q : M) (v : TangentSpace (𝓡 n) q)
    {x : M} (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source) :
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm (extChartAt (𝓡 n) q x) v := by
  let tr := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) q
  have hself : (tr ⟨q, v⟩).2 = v := by
    rw [← tr.continuousLinearMapAt_apply_of_mem ℝ
      (FiberBundle.mem_baseSet_trivializationAt' q) v]
    change (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q).continuousLinearMapAt ℝ q v = v
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source _ _),
      mfderiv_extChartAt_self]
    rfl
  change tr.symm x ((tr ⟨q, v⟩).2) = _
  rw [hself, ← tr.symmL_apply (R := ℝ) hx]
  have he := TangentBundle.symmL_trivializationAt (I := 𝓡 n) hx
  simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ, tr] using!
    congrArg (fun D ↦ D v) he

set_option backward.isDefEq.respectTransparency false in

theorem preferredField_pullback (q : M) (v : TangentSpace (𝓡 n) q)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q).target) :
    VectorField.mpullbackWithin (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) univ y = v := by
  have hx : (extChartAt (𝓡 n) q).symm y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source := by
    simpa only [extChartAt_source] using (extChartAt (𝓡 n) q).map_target hy
  rw [VectorField.mpullbackWithin_apply,
    preferredField_eq_inverseChartDerivative q v hx,
    (extChartAt (𝓡 n) q).right_inv hy]
  have hi := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) hy
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hi ⊢
  exact hi.inverse_apply_eq.mpr rfl

set_option backward.isDefEq.respectTransparency false in

theorem preferredFields_mlieBracket_eq_zero (q : M) (v w : TangentSpace (𝓡 n) q) :
    VectorField.mlieBracket (𝓡 n)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) q = 0 := by
  have hg (a : TangentSpace (𝓡 n) q) :
      VectorField.mpullbackWithin (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) univ =ᶠ[𝓝 (extChartAt (𝓡 n) q q)]
          (fun _ ↦ a) := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓡 n) q] with y hy
    exact preferredField_pullback q a hy
  rw [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply]
  simp only [modelWithCornersSelf_coe, range_id, preimage_univ, inter_univ,
    mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id,
    VectorField.lieBracketWithin_univ]
  rw [(hg v).lieBracket_vectorField_eq (hg w)]
  simp [VectorField.lieBracket]

set_option backward.isDefEq.respectTransparency false in

theorem preferredField_scalar_derivative {f : M → ℝ} (q : M)
    (v : TangentSpace (𝓡 n) q) {x : M}
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source)
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f x) :
    fderiv ℝ (f ∘ (extChartAt (𝓡 n) q).symm) (extChartAt (𝓡 n) q x) v =
      mvfderiv (𝓡 n) f x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x) := by
  have hx' : x ∈ (extChartAt (𝓡 n) q).source := by
    simpa only [extChartAt_source] using hx
  have he : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm
      (extChartAt (𝓡 n) q x) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 n)
        ((extChartAt (𝓡 n) q).map_source hx'))
  have hc := mfderiv_comp_apply_of_eq (extChartAt (𝓡 n) q x) hf he
    ((extChartAt (𝓡 n) q).left_inv hx') v
  rw [mfderiv_eq_fderiv] at hc
  rw [preferredField_eq_inverseChartDerivative q v hx]
  exact hc


theorem preferredChart_scalar_derivative {f : M → ℝ} (q : M)
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f q) (v : TangentSpace (𝓡 n) q) :
    fderiv ℝ (f ∘ (extChartAt (𝓡 n) q).symm) (extChartAt (𝓡 n) q q) v =
      mvfderiv (𝓡 n) f q v := by
  simpa only [FiberBundle.extend_apply_self] using
    preferredField_scalar_derivative q v (mem_chart_source _ _) hf

end PoincareConjecture.M10
