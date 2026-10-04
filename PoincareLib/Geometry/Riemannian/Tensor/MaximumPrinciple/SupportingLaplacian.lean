import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.Contact
import PoincareLib.Geometry.Riemannian.ScalarOperators.Extrema
import PoincareLib.Geometry.Riemannian.ScalarOperators.Locality
import PoincareLib.Geometry.Riemannian.ScalarOperators.Scaling
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Local supporting-functional Laplacian estimates

Finite linear combinations of tensor evaluations give scalar supporting
functionals. Their Laplacian agrees with the corresponding rough-Laplacian
contraction when the local input fields have vanishing first and diagonal
second covariant jets. A scalar localization argument then supplies the sign
at a local maximum, using the scalar extrema theorem.

Source: Morgan--Tian, Claim 4.2, printed p. 64; Theorems 4.7--4.8, p. 66.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter Set

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- A smooth function on a neighborhood has nonpositive Laplacian at a local
maximum. The bump extension allows use of the global scalar extrema theorem. -/
lemma laplacian_nonpos_of_isLocalMaxOn_open [T2Space M]
    (D : LeviCivitaData g) {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U)
    (hmax : IsLocalMax f x) : D.laplacian f x ≤ 0 := by
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (hU.mem_nhds hx)
  let F : M → ℝ := fun y => b y * f y
  have hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F := by
    apply contMDiff_of_tsupport
    intro y hy
    have hyU : y ∈ U := hb (tsupport_mul_subset_left hy)
    exact b.contMDiffAt.mul ((hf y hyU).contMDiffAt (hU.mem_nhds hyU))
  have heq : F =ᶠ[𝓝 x] f := by
    filter_upwards [b.eventuallyEq_one] with y hy
    simp only [F, hy, Pi.one_apply, one_mul]
  have hmaxF : IsLocalMax F x := by
    filter_upwards [heq, hmax] with y hy hmaxy
    simpa only [hy, heq.self_of_nhds] using hmaxy
  rw [← D.laplacian_eq_of_eventuallyEq heq]
  exact D.laplacian_nonpos_of_isLocalMax hF hmaxF

private lemma hessian_sum_on_open (D : LeviCivitaData g) {J : Type} [Fintype J]
    (f : J → M → ℝ) {U : Set M} (hU : IsOpen U)
    (hf : ∀ j, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j) U)
    {x : M} (hx : x ∈ U) (a b : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => ∑ j, f j y) x a b = ∑ j, D.hessian (f j) x a b := by
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) (k := ∞) b
  have hfx j := (hf j x hx).contMDiffAt (hU.mem_nhds hx)
  have hi : (fun y => mvfderiv (𝓡 n) (fun z => ∑ j, f j z) y (Y y)) =ᶠ[𝓝 x]
      (fun y => ∑ j, mvfderiv (𝓡 n) (f j) y (Y y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact mvfderiv_sum_apply f y (Y y) fun j =>
      ((hf j y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hdiff (j : J) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => mvfderiv (𝓡 n) (f j) y (Y y)) x :=
    (contMDiffAt_mvfderiv_apply (hfx j) hY).mdifferentiableAt (by simp)
  simp only [hessian, hessianOnFields, FiberBundle.extend_apply_self]
  change mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) (fun z => ∑ j, f j z) y (Y y)) x a -
      mvfderiv (𝓡 n) (fun y => ∑ j, f j y) x (D.connection Y x a) = _
  rw [Poincare.mvfderiv_eq_of_eventuallyEq hi, mvfderiv_sum_apply _ x a hdiff,
    mvfderiv_sum_apply f x (D.connection Y x a)
      (fun j => (hfx j).mdifferentiableAt (by simp)), Finset.sum_sub_distrib]

/-- The scalar Laplacian commutes with finite sums of locally smooth functions. -/
lemma laplacian_sum_on_open (D : LeviCivitaData g) {J : Type} [Fintype J]
    (f : J → M → ℝ) {U : Set M} (hU : IsOpen U)
    (hf : ∀ j, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j) U)
    {x : M} (hx : x ∈ U) :
    D.laplacian (fun y => ∑ j, f j y) x = ∑ j, D.laplacian (f j) x := by
  simp only [laplacian, D.hessian_sum_on_open f hU hf hx]
  exact Finset.sum_comm

/-- A finite supporting-functional contraction has the scalar Laplacian of
its local contact function when the input fields have the required zero jets. -/
theorem sum_tensorLaplacian_eq_laplacian_of_zero_jets
    (D : LeviCivitaData g) {J : Type} [Fintype J] {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (c : J → ℝ) (W : J → Fin k → (y : M) → TangentSpace (𝓡 n) y)
    {U : Set M} (hU : IsOpen U)
    (hW : ∀ j i, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W j i)) U)
    {x : M} (hx : x ∈ U)
    (hfirst : ∀ j i v, D.connection (W j i) x v = 0)
    (hsecond : ∀ j i v, D.connection
      (D.covariantDerivativeOnFields
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) (W j i)) x v = 0) :
    (∑ j, c j * D.tensorLaplacian T x (fun i => W j i x)) =
      D.laplacian (fun y => ∑ j, c j * T y (fun i => W j i y)) x := by
  have hsmooth j := (contMDiffOn_const (c := c j)).mul (hT.2 U hU (W j) (hW j))
  rw [D.laplacian_sum_on_open (fun j y => c j * T y (fun i => W j i y)) hU hsmooth hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [D.laplacian_const_mul, D.tensorLaplacian_eq_laplacian_of_zero_jets hT (W j) x
    (fun i => (hW j i x hx).contMDiffAt (hU.mem_nhds hx)) (hfirst j) (hsecond j)]

/-- Local supporting-function maxima give the nonpositive rough-Laplacian
contribution for every finite linear contraction of the tensor. -/
theorem sum_tensorLaplacian_nonpos_of_isLocalMax [T2Space M]
    (D : LeviCivitaData g) {J : Type} [Fintype J] {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (c : J → ℝ) (W : J → Fin k → (y : M) → TangentSpace (𝓡 n) y)
    {U : Set M} (hU : IsOpen U)
    (hW : ∀ j i, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W j i)) U)
    {x : M} (hx : x ∈ U)
    (hfirst : ∀ j i v, D.connection (W j i) x v = 0)
    (hsecond : ∀ j i v, D.connection
      (D.covariantDerivativeOnFields
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) (W j i)) x v = 0)
    (hmax : IsLocalMax (fun y => ∑ j, c j * T y (fun i => W j i y)) x) :
    (∑ j, c j * D.tensorLaplacian T x (fun i => W j i x)) ≤ 0 := by
  rw [D.sum_tensorLaplacian_eq_laplacian_of_zero_jets hT c W hU hW hx hfirst hsecond]
  apply D.laplacian_nonpos_of_isLocalMaxOn_open hU _ hx hmax
  intro y hy
  exact ContMDiffWithinAt.sum fun j _ =>
    contMDiffWithinAt_const.mul (hT.2 U hU (W j) (hW j) y hy)

end PoincareMT.LeviCivitaData
