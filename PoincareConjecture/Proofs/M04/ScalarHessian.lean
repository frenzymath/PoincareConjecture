import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure
import Mathlib.Geometry.Manifold.BumpFunction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter Function

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private def scalarEvaluation (q : M → ℝ) : CovariantTensorEvaluation n M 0 := fun x _ ↦ q x

private theorem isSmoothCovariantTensor_scalarEvaluation {q : M → ℝ}
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) :
    IsSmoothCovariantTensor (scalarEvaluation (n := n) (M := M) q) := by
  constructor
  · intro x
    exact ⟨MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 ↦ TangentSpace (𝓡 n) x) (q x),
      fun _ ↦ rfl⟩
  · intro U hU X hX
    exact hq.contMDiffOn

private theorem derivative_scalarEvaluation (D : LeviCivitaData g) (q : M → ℝ) (x : M)
    (v : Fin 1 → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (scalarEvaluation (n := n) (M := M) q) x v =
      mvfderiv (𝓡 n) q x (v 0) := by
  simp [LeviCivitaData.covariantTensorDerivative, scalarEvaluation]

private theorem second_derivative_scalarEvaluation (D : LeviCivitaData g) (q : M → ℝ)
    (x : M) (v : Fin 2 → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative
      (D.covariantTensorDerivative (scalarEvaluation (n := n) (M := M) q)) x v =
      D.hessian q x (v 0) (v 1) := by
  have h01 : (Fin.succ 0 : Fin 2) = 1 := by decide
  rw [LeviCivitaData.covariantTensorDerivative]
  simp only [derivative_scalarEvaluation, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Function.update_self, LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self, add_zero, h01]

theorem isSmoothCovariantTensor_hessian (D : LeviCivitaData g) {q : M → ℝ}
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) :
    IsSmoothCovariantTensor (k := 2) (fun x v ↦ D.hessian q x (v 0) (v 1)) := by
  have hs := isSmoothCovariantTensor_covariantTensorDerivative D
    (isSmoothCovariantTensor_covariantTensorDerivative D
      (isSmoothCovariantTensor_scalarEvaluation (n := n) (M := M) hq))
  have heq : D.covariantTensorDerivative
      (D.covariantTensorDerivative (scalarEvaluation (n := n) (M := M) q)) =
      (fun x v ↦ D.hessian q x (v 0) (v 1)) :=
    funext fun x ↦ funext fun v ↦ second_derivative_scalarEvaluation D q x v
  rwa [heq] at hs

set_option backward.isDefEq.respectTransparency false in
private theorem hessianOnFields_eq_hessian_global (D : LeviCivitaData g)
    {q : M → ℝ} (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q)
    {U : Set M} {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    {x : M} (hx : x ∈ U) :
    D.hessianOnFields q X Y x = D.hessian q x (X x) (Y x) := by
  have hs := isSmoothCovariantTensor_covariantTensorDerivative D
    (isSmoothCovariantTensor_scalarEvaluation (n := n) (M := M) hq)
  have he := covariantTensorDerivativeOnFields_eq D hs hU (X := ![X, Y])
    (by
      intro i
      fin_cases i
      · exact hX
      · exact hY) hx
  have h01 : (Fin.succ 0 : Fin 2) = 1 := by decide
  simp only [covariantTensorDerivativeOnFields, derivative_scalarEvaluation,
    second_derivative_scalarEvaluation, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Function.update_self, add_zero, h01] at he
  simpa [LeviCivitaData.hessianOnFields] using he

private theorem hessianOnFields_congr_germ (D : LeviCivitaData g) {q r : M → ℝ} {x : M}
    (h : q =ᶠ[𝓝 x] r) (X Y : (y : M) → TangentSpace (𝓡 n) y) :
    D.hessianOnFields q X Y x = D.hessianOnFields r X Y x := by
  have he : (fun y ↦ mvfderiv (𝓡 n) q y (Y y)) =ᶠ[𝓝 x]
      (fun y ↦ mvfderiv (𝓡 n) r y (Y y)) := by
    filter_upwards [h.eventually_nhds] with y hy
    have hd : mvfderiv (𝓡 n) q y = mvfderiv (𝓡 n) r y :=
      Filter.EventuallyEq.mfderiv_eq hy
    exact congrArg (fun A ↦ A (Y y)) hd
  have hd : mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) q y (Y y)) x =
      mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) r y (Y y)) x := he.mfderiv_eq
  have hx : mvfderiv (𝓡 n) q x = mvfderiv (𝓡 n) r x := h.mfderiv_eq
  simp only [LeviCivitaData.hessianOnFields, hd, hx]

private theorem hessian_congr_germ (D : LeviCivitaData g) {q r : M → ℝ} {x : M}
    (h : q =ᶠ[𝓝 x] r) (a b : TangentSpace (𝓡 n) x) :
    D.hessian q x a b = D.hessian r x a b :=
  hessianOnFields_congr_germ D h _ _

private theorem exists_smooth_scalar_localization [T2Space M]
    {U : Set M} {q : M → ℝ} {x : M} (hU : IsOpen U)
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) (hx : x ∈ U) :
    ∃ q0 : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q0 ∧ q0 =ᶠ[𝓝 x] q := by
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (hU.mem_nhds hx)
  refine ⟨fun y ↦ b y • q y, ?_, ?_⟩
  · apply contMDiff_of_tsupport
    intro y hy
    have hyU : y ∈ U := hb (tsupport_smul_subset_left (fun y ↦ b y) q hy)
    exact b.contMDiffAt.smul ((hq y hyU).contMDiffAt (hU.mem_nhds hyU))
  · filter_upwards [b.eventuallyEq_one] with y hy
    change b y = 1 at hy
    rw [hy, one_smul]

theorem hessianOnFields_eq_hessian_of_contMDiffOn [T2Space M] (D : LeviCivitaData g)
    {U : Set M} {q : M → ℝ} {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hU : IsOpen U) (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    {x : M} (hx : x ∈ U) :
    D.hessianOnFields q X Y x = D.hessian q x (X x) (Y x) := by
  obtain ⟨q0, hq0, heq⟩ := exists_smooth_scalar_localization hU hq hx
  calc
    _ = D.hessianOnFields q0 X Y x := hessianOnFields_congr_germ D heq.symm X Y
    _ = D.hessian q0 x (X x) (Y x) := hessianOnFields_eq_hessian_global D hq0 hU hX hY hx
    _ = _ := hessian_congr_germ D heq (X x) (Y x)

theorem exists_hessian_bilinear_of_contMDiffOn [T2Space M] (D : LeviCivitaData g)
    {U : Set M} {q : M → ℝ} {x : M} (hU : IsOpen U)
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) (hx : x ∈ U) :
    ∃ A : MultilinearMap ℝ (fun _ : Fin 2 ↦ TangentSpace (𝓡 n) x) ℝ,
      ∀ v, D.hessian q x (v 0) (v 1) = A v := by
  obtain ⟨q0, hq0, heq⟩ := exists_smooth_scalar_localization hU hq hx
  obtain ⟨A, hA⟩ := (isSmoothCovariantTensor_hessian D hq0).1 x
  exact ⟨A, fun v ↦ (hessian_congr_germ D heq.symm (v 0) (v 1)).trans (hA v)⟩

theorem hessianOnFields_eq_hessian_of_contMDiff (D : LeviCivitaData g)
    {q : M → ℝ} (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q)
    {U : Set M} {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    {x : M} (hx : x ∈ U) :
    D.hessianOnFields q X Y x = D.hessian q x (X x) (Y x) :=
  hessianOnFields_eq_hessian_global D hq hU hX hY hx

end PoincareConjecture.M04
