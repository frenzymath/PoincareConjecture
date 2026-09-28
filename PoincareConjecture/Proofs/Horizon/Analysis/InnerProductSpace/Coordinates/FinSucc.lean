import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations








set_option autoImplicit false

open scoped ContDiff

namespace Poincare.EuclideanSpace


def euclideanCons {n : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons t (WithLp.ofLp y))

@[simp]
lemma euclideanCons_zero {n : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    euclideanCons t y 0 = t := rfl

@[simp]
lemma euclideanCons_succ {n : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanCons t y i.succ = y i := rfl


def euclideanTail {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => x i.succ)

@[simp]
lemma euclideanTail_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    euclideanTail x i = x i.succ := rfl

@[simp]
lemma euclideanTail_cons {n : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    euclideanTail (euclideanCons t y) = y := by
  ext i
  rfl

@[simp]
lemma euclideanCons_tail {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    euclideanCons (x 0) (euclideanTail x) = x := by
  ext i
  cases i using Fin.cases <;> rfl


noncomputable def euclideanConsCLE (n : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => euclideanCons p.1 p.2
      invFun := fun x => (x 0, euclideanTail x)
      left_inv := by intro p; simp
      right_inv := euclideanCons_tail
      map_add' := by
        intro p q
        ext i
        cases i using Fin.cases <;> simp
      map_smul' := by
        intro c p
        ext i
        cases i using Fin.cases <;> simp }

@[simp]
lemma euclideanConsCLE_apply {n : ℕ} (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    euclideanConsCLE n p = euclideanCons p.1 p.2 := rfl

@[simp]
lemma euclideanConsCLE_symm_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    (euclideanConsCLE n).symm x = (x 0, euclideanTail x) := rfl


noncomputable def euclideanTailProjectionCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := euclideanTail
      map_add' := by intro v w; ext i; rfl
      map_smul' := by intro c v; ext i; rfl }

@[simp]
lemma euclideanTailProjectionCLM_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    euclideanTailProjectionCLM n x = euclideanTail x := rfl

lemma contDiff_euclideanTail (n : ℕ) : ContDiff ℝ ∞ (euclideanTail (n := n)) :=
  (euclideanTailProjectionCLM n).contDiff

lemma continuous_euclideanTail (n : ℕ) : Continuous (euclideanTail (n := n)) :=
  (euclideanTailProjectionCLM n).continuous


noncomputable def euclideanTailCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := euclideanCons 0
      map_add' := by
        intro v w
        ext i
        cases i using Fin.cases <;> simp [euclideanCons]
      map_smul' := by
        intro c v
        ext i
        cases i using Fin.cases <;> simp [euclideanCons] }

@[simp]
lemma euclideanTailCLM_apply {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    euclideanTailCLM n y = euclideanCons 0 y := rfl

lemma euclideanTailCLM_injective (n : ℕ) : Function.Injective (euclideanTailCLM n) := by
  intro v w h
  ext i
  exact congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x i.succ) h

lemma euclideanCons_eq_add {n : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    euclideanCons t y = euclideanCons t 0 + euclideanTailCLM n y := by
  ext i
  cases i using Fin.cases <;> simp

@[simp]
lemma euclideanTailCLM_basisFun {n : ℕ} (i : Fin n) :
    euclideanTailCLM n (EuclideanSpace.basisFun (Fin n) ℝ i) =
      EuclideanSpace.basisFun (Fin (n + 1)) ℝ i.succ := by
  ext j
  cases j using Fin.cases <;> simp [EuclideanSpace.basisFun_apply]

lemma contDiff_euclideanCons {n : ℕ} (t : ℝ) :
    ContDiff ℝ ∞ (euclideanCons (n := n) t) := by
  have hfun : euclideanCons t =
      (fun y : EuclideanSpace ℝ (Fin n) => euclideanCons t 0 + euclideanTailCLM n y) := by
    funext y
    exact euclideanCons_eq_add t y
  rw [hfun]
  simpa only [Pi.add_apply] using contDiff_const.add (euclideanTailCLM n).contDiff

set_option backward.isDefEq.respectTransparency false in
lemma hasFDerivAt_euclideanCons {n : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (euclideanCons t) (euclideanTailCLM n) y := by
  have h := (hasFDerivAt_const (euclideanCons t 0) y).add
    (euclideanTailCLM n).hasFDerivAt
  have hfun : euclideanCons t =
      (fun y : EuclideanSpace ℝ (Fin n) => euclideanCons t 0 + euclideanTailCLM n y) := by
    funext z
    exact euclideanCons_eq_add t z
  rw [hfun]
  convert h using 1 <;> first | rfl | simp

lemma fderiv_euclideanCons {n : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (euclideanCons t) y = euclideanTailCLM n :=
  (hasFDerivAt_euclideanCons t y).fderiv

end Poincare.EuclideanSpace
