
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.RicciDerivative
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

section LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]


def bilinearOfTwoTensor (A : MultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ := by
  have hu0 (a b c : E) : Function.update ![a, b] 0 c = ![c, b] := by
    ext i
    fin_cases i <;> simp
  have hu1 (a b c : E) : Function.update ![a, b] 1 c = ![a, c] := by
    ext i
    fin_cases i <;> simp
  exact LinearMap.mk₂ ℝ (fun a b ↦ A ![a, b])
    (fun a a' b ↦ by
      simpa only [MultilinearMap.toLinearMap_apply, hu0] using
        (A.toLinearMap ![a, b] 0).map_add a a')
    (fun c a b ↦ by
      simpa only [MultilinearMap.toLinearMap_apply, hu0] using
        (A.toLinearMap ![a, b] 0).map_smul c a)
    (fun a b b' ↦ by
      simpa only [MultilinearMap.toLinearMap_apply, hu1] using
        (A.toLinearMap ![a, b] 1).map_add b b')
    (fun c a b ↦ by
      simpa only [MultilinearMap.toLinearMap_apply, hu1] using
        (A.toLinearMap ![a, b] 1).map_smul c b)

@[simp]
lemma bilinearOfTwoTensor_apply (A : MultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ)
    (a b : E) : bilinearOfTwoTensor A a b = A ![a, b] := rfl


lemma bilinear_sum_orthonormalBasis_eq (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    ∑ i, B (b i) (b i) = ∑ j, B (c j) (c j) := by
  classical
  have hexpand (j : κ) : B (c j) (c j) =
      ∑ i, ∑ k, (inner ℝ (b i) (c j) * inner ℝ (b k) (c j)) * B (b i) (b k) := by
    conv_lhs => rw [← b.sum_repr' (c j)]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext k
    ring
  symm
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hcoeff (k : ι) :
      ∑ j, inner ℝ (b i) (c j) * inner ℝ (b k) (c j) = inner ℝ (b i) (b k) := by
    simpa only [real_inner_comm (b k) (c _)] using c.sum_inner_mul_inner (b i) (b k)
  simp_rw [hcoeff]
  simp [b.inner_eq_ite]


lemma bilinear_sum_frame_corrections (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (C : ι → E) :
    (∑ i, (B (C i) (b i) + B (b i) (C i))) =
      ∑ i, ∑ j, (inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) * B (b i) (b j) := by
  have hleft (i : ι) : B (C i) (b i) =
      ∑ j, inner ℝ (C i) (b j) * B (b j) (b i) := by
    conv_lhs => rw [← b.sum_repr' (C i)]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [real_inner_comm (b _) (C i)]
  have hright (i : ι) : B (b i) (C i) =
      ∑ j, inner ℝ (b j) (C i) * B (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr' (C i)]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hleft, hright, Finset.sum_add_distrib, add_mul]
  rw [Finset.sum_comm (f := fun i j ↦ inner ℝ (C i) (b j) * B (b j) (b i))]
  simp_rw [real_inner_comm (C _) (b _)]
  rw [add_comm]
  simp_rw [Finset.sum_add_distrib]


lemma bilinear_sum_basis_eq_inverse_gram [DecidableEq ι]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (b : Module.Basis ι ℝ E)
    (c : OrthonormalBasis κ ℝ E) :
    (∑ a, B (c a) (c a)) =
      ∑ i, ∑ j, (Matrix.of (fun i j ↦ inner ℝ (b i) (b j)))⁻¹ i j * B (b i) (b j) := by
  classical
  let G : Matrix ι ι ℝ := fun i j ↦ inner ℝ (b i) (b j)
  let C : Matrix ι ι ℝ := fun i j ↦ ∑ a, b.repr (c a) i * b.repr (c a) j
  have hGC : G * C = 1 := by
    ext i j
    change (∑ k, inner ℝ (b i) (b k) * ∑ a, b.repr (c a) k * b.repr (c a) j) = _
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have hinner (a : κ) :
        ∑ k, inner ℝ (b i) (b k) * b.repr (c a) k = inner ℝ (b i) (c a) := by
      conv_rhs => rw [← b.sum_repr (c a)]
      simp only [inner_sum, real_inner_smul_right, mul_comm]
    simp_rw [hinner]
    have h := congrArg (fun w ↦ b.repr w j) (c.sum_repr' (b i))
    simpa [map_sum, map_smul, real_inner_comm (c _) (b i), mul_comm,
      Matrix.one_apply, Finsupp.single_apply, eq_comm] using h
  have hC : G⁻¹ = C := Matrix.inv_eq_right_inv hGC
  change _ = ∑ i, ∑ j, G⁻¹ i j * B (b i) (b j)
  rw [hC]
  have hexpand (a : κ) : B (c a) (c a) =
      ∑ i, ∑ j, (b.repr (c a) i * b.repr (c a) j) * B (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr (c a)]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [C, Finset.sum_mul]

end LinearAlgebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


lemma IsSmoothCovariantTensor.contMDiffAt_extend {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun y ↦ T y (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)) x := by
  classical
  choose s hs hsm using fun i ↦
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (v i)
  let U : Set M := ⋂ i, interior (s i)
  have hU : IsOpen U := isOpen_iInter_of_finite fun _ ↦ isOpen_interior
  have hx : x ∈ U := by
    exact Set.mem_iInter.mpr fun i ↦ mem_interior_iff_mem_nhds.mpr (hs i)
  apply (hT.2 U hU
    (fun i y ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y) ?_).contMDiffAt
    (hU.mem_nhds hx)
  intro i
  exact (hsm i).mono fun y hy ↦ interior_subset (Set.mem_iInter.mp hy i)

namespace LeviCivitaData

set_option backward.isDefEq.respectTransparency false in
lemma mvfderiv_sum_apply {ι : Type} [Fintype ι]
    (f : ι → M → ℝ) (x : M) (v : TangentSpace (𝓡 n) x)
    (hf : ∀ i, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (f i) x) :
    mvfderiv (𝓡 n) (fun y ↦ ∑ i, f i y) x v =
      ∑ i, mvfderiv (𝓡 n) (f i) x v := by
  have h : HasMFDerivAt (𝓡 n) (𝓘(ℝ, ℝ)) (∑ i, f i) x
      (∑ i, mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) (f i) x) :=
    HasMFDerivAt.sum (fun i _ ↦ (hf i).hasMFDerivAt)
  have h' := DFunLike.congr_fun h.mfderiv v
  change (mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ ∑ i, f i y) x) v =
    ∑ i, (mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) (f i) x) v
  have heq : (∑ i, f i) = (fun y ↦ ∑ i, f i y) := by
    ext y
    simp
  rw [heq] at h'
  let ds : ι → TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
    fun i ↦ mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) (f i) x
  have hs : (∑ i, ds i) v = ∑ i, ds i v := sum_apply Finset.univ ds v
  exact h'.trans hs


lemma mvfderiv_metric_extend (D : LeviCivitaData g) (x : M)
    (v a b : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n)
      (fun y ↦ g.inner y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a y)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b y)) x v =
      g.inner x
        (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) x v) b +
      g.inner x a
        (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b) x v) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := D.connection.derivMetricTensor_apply_eq_extend v a b
  rw [D.metricCompatible] at h
  change 0 = _ at h
  change (0 : ℝ) = mvfderiv (𝓡 n)
    (fun y ↦ g.inner y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b y)) x v -
    g.inner x (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) x v) b -
    g.inner x a (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b) x v) at h
  linarith


lemma covariantTensorDerivative_metric_eq_zero (D : LeviCivitaData g)
    (x : M) (v a b : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w ↦ g.inner y (w 0) (w 1)) x ![v, a, b] = 0 := by
  simp only [covariantTensorDerivative, Fin.sum_univ_two]
  simp
  exact sub_eq_zero.mpr (D.mvfderiv_metric_extend x v a b)




lemma sum_covariantTensorDerivative_eq_fixed_trace_sub_gram
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 2}
    (hT : IsSmoothCovariantTensor T) (x : M) (v : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let X := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    (∑ i, D.covariantTensorDerivative T x ![v, b i, b i]) =
      mvfderiv (𝓡 n) (fun y ↦ ∑ i, T y ![X i y, X i y]) x v -
        ∑ i, ∑ j, mvfderiv (𝓡 n) (fun y ↦ g.inner y (X i y) (X j y)) x v *
          T x ![b i, b j] := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let b := g.orthonormalBasis x
  let X := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  change (∑ i, D.covariantTensorDerivative T x ![v, b i, b i]) =
    mvfderiv (𝓡 n) (fun y ↦ ∑ i, T y ![X i y, X i y]) x v -
      ∑ i, ∑ j, mvfderiv (𝓡 n) (fun y ↦ g.inner y (X i y) (X j y)) x v *
        T x ![b i, b j]
  have heval (i) : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun y ↦ T y ![X i y, X i y]) x := by
    convert (hT.contMDiffAt_extend x ![b i, b i]).mdifferentiableAt (by simp) using 1
    ext y
    congr 1
    ext j
    fin_cases j <;> rfl
  rw [mvfderiv_sum_apply _ x v heval]
  rcases hT.1 x with ⟨A, hA⟩
  have hc := bilinear_sum_frame_corrections (bilinearOfTwoTensor A) b
    (fun i ↦ D.connection (X i) x v)
  simp only [bilinearOfTwoTensor_apply, ← hA] at hc
  have hmetric (i j) :
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (X i y) (X j y)) x v =
        inner ℝ (D.connection (X i) x v) (b j) +
        inner ℝ (b i) (D.connection (X j) x v) :=
    D.mvfderiv_metric_extend x v (b i) (b j)
  simp_rw [hmetric]
  rw [← hc, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [covariantTensorDerivative, Fin.sum_univ_two]
  simp
  congr 1
  · congr 2
    ext y
    congr 1
    ext j
    fin_cases j <;> rfl
  · congr 1 <;> congr 1 <;> ext j <;> fin_cases j <;> simp [X]


end LeviCivitaData

end PoincareConjecture
