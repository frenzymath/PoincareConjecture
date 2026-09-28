import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic.Module



set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.LinearTorus

variable (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ)


def integerMatrixHom : (AddCircle p × AddCircle p) →+ (AddCircle p × AddCircle p) where
  toFun x := (A 0 0 • x.1 + A 0 1 • x.2, A 1 0 • x.1 + A 1 1 • x.2)
  map_zero' := by simp
  map_add' x y := by ext <;> simp <;> abel

@[simp] theorem integerMatrixHom_apply (x : AddCircle p × AddCircle p) :
    integerMatrixHom p A x =
      (A 0 0 • x.1 + A 0 1 • x.2, A 1 0 • x.1 + A 1 1 • x.2) := rfl

theorem continuous_integerMatrixHom : Continuous (integerMatrixHom p A) := by
  change Continuous (fun x : AddCircle p × AddCircle p =>
    (A 0 0 • x.1 + A 0 1 • x.2, A 1 0 • x.1 + A 1 1 • x.2))
  fun_prop


def integerMatrixMap : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p) :=
  ⟨integerMatrixHom p A, continuous_integerMatrixHom p A⟩

@[simp] theorem integerMatrixMap_apply (x : AddCircle p × AddCircle p) :
    integerMatrixMap p A x =
      (A 0 0 • x.1 + A 0 1 • x.2, A 1 0 • x.1 + A 1 1 • x.2) := rfl

@[simp] theorem integerMatrixMap_apply_coe (x y : ℝ) :
    integerMatrixMap p A ((x : AddCircle p), (y : AddCircle p)) =
      ((((A 0 0 : ℝ) * x + (A 0 1 : ℝ) * y : ℝ) : AddCircle p),
       (((A 1 0 : ℝ) * x + (A 1 1 : ℝ) * y : ℝ) : AddCircle p)) := by
  simp [integerMatrixMap_apply, ← zsmul_eq_mul]

theorem integerMatrixHom_adjugate (x : AddCircle p × AddCircle p) :
    integerMatrixHom p A (integerMatrixHom p A.adjugate x) = A.det • x := by
  ext <;> simp [Matrix.adjugate_fin_two, Matrix.det_fin_two] <;> module

theorem adjugate_integerMatrixHom (x : AddCircle p × AddCircle p) :
    integerMatrixHom p A.adjugate (integerMatrixHom p A x) = A.det • x := by
  ext <;> simp [Matrix.adjugate_fin_two, Matrix.det_fin_two] <;> module

theorem surjective_integerMatrixHom (hA : A.det ≠ 0) :
    Function.Surjective (integerMatrixHom p A) := by
  have hd : IsUnit (A.det : ℝ) := isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hA)
  have hs := (AddCircle.isAddQuotientCoveringMap_zsmul p hd).surjective
  intro y
  obtain ⟨x₁, hx₁⟩ := hs y.1
  obtain ⟨x₂, hx₂⟩ := hs y.2
  refine ⟨integerMatrixHom p A.adjugate (x₁, x₂), ?_⟩
  rw [integerMatrixHom_adjugate]
  exact Prod.ext hx₁ hx₂

theorem finite_ker_integerMatrixHom (hA : A.det ≠ 0) :
    Set.Finite ((integerMatrixHom p A).ker : Set (AddCircle p × AddCircle p)) := by
  have hd : IsSMulRegular ℝ A.det := by
    intro x y h
    exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hA) (by simpa only [zsmul_eq_mul] using h)
  have ht := AddCircle.finite_torsion_of_isSMulRegular_int p A.det hd
  apply (ht.prod ht).subset
  intro x hx
  have h := adjugate_integerMatrixHom p A x
  rw [AddMonoidHom.mem_ker.mp hx, map_zero] at h
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

theorem isCoveringMap_integerMatrixMap (hp : 0 < p) (hA : A.det ≠ 0) :
    IsCoveringMap (integerMatrixMap p A) := by
  let : Fact (0 < p) := ⟨hp⟩
  have hq : IsQuotientMap (integerMatrixHom p A) :=
    .of_surjective_continuous (surjective_integerMatrixHom p A hA)
      (continuous_integerMatrixHom p A)
  exact (hq.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom
    (finite_ker_integerMatrixHom p A hA).isDiscrete).isCoveringMap

end PoincareConjecture.M76.LinearTorus
