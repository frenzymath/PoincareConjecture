import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Spacetime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set Filter

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


lemma contMDiffAt_hessian_scalarCurvature_fields
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X : Fin 2 → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).hessian
        (F.connection p.1).scalarCurvature p.2 (X 0 p.2) (X 1 p.2)) (t, x) := by
  have hspace (s : ℝ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (F.connection s).scalarCurvature := by
    intro y
    have h := ((hC.tensor_calculus n M (F.metric s) (F.connection s)).2.1.tensorTrace
      (g := F.metric s)).contMDiffAt_apply (x := y)
        (X := fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
    convert h using 1
    funext z
    unfold RiemannianMetric.tensorTrace LeviCivitaData.scalarCurvature
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hscalar : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (t, x) :=
    (hC.scalar_regular n M J F (t, x) ⟨interior_subset ht, mem_univ x⟩).contMDiffAt
      (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) Filter.univ_mem)
  have hreg (Y : Fin 1 → (y : M) → TangentSpace (𝓡 n) y)
      (hY : ∀ i, ContMDiffAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (Y i)) x) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => differentialEvaluation (F.connection p.1).scalarCurvature
          p.2 (fun i => Y i p.2)) (t, x) := by
    change ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => mvfderiv (𝓡 n) (F.connection p.1).scalarCurvature
        p.2 (Y 0 p.2)) (t, x)
    exact Poincare.Manifold.contMDiffAt_mvfderiv_spatial (I := 𝓡 n)
      (f := fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2)
      (X := Y 0) hscalar (hY 0)
  have h := F.contMDiffAt_covariantTensorDerivative_fields (k := 1) (X := X)
    (T := fun s => differentialEvaluation (F.connection s).scalarCurvature) ht
    (fun s => differentialEvaluation_isSmooth (hspace s)) hreg hX
  convert h using 1
  funext p
  rw [LeviCivitaData.hessian_eq_covariantTensorDerivative]
  congr 1
  ext i
  fin_cases i <;> rfl



lemma contMDiffAt_ricciSquare_fields
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X : Fin 2 → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ i,
        (F.connection p.1).ricci p.2 (X 0 p.2) ((F.metric p.1).orthonormalBasis p.2 i) *
        (F.connection p.1).ricci p.2 ((F.metric p.1).orthonormalBasis p.2 i) (X 1 p.2))
      (t, x) := by
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2, 0, 1, 3] (by decide)
  let S : ℝ → CovariantTensorEvaluation n M 4 := fun s y z =>
    tensorProduct (F.connection s).ricciEvaluation (F.connection s).ricciEvaluation
      y (z ∘ σ)
  have hS (s : ℝ) : IsSmoothCovariantTensor (S s) :=
    (isSmoothCovariantTensor_tensorProduct
      (hC.tensor_calculus n M (F.metric s) (F.connection s)).2.1
      (hC.tensor_calculus n M (F.metric s) (F.connection s)).2.1).perm σ
  have h := F.contMDiffAt_tensorTrace_fields (T := S) ht hS
    (fun Y hY => (F.contMDiffAt_ricci_fields ht (hY (σ 0)) (hY (σ 1))).mul
      (F.contMDiffAt_ricci_fields ht (hY (σ 2)) (hY (σ 3)))) hX
  exact h



lemma contMDiffAt_hamiltonM_fields
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0) {x : M}
    {X : Fin 2 → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => hamiltonM (F.connection p.1) (p.1 - T₀) p.2
        (X 0 p.2) (X 1 p.2)) (t, x) := by
  have hRic := F.contMDiffAt_ricci_fields ht (hX 0) (hX 1)
  have hdRic := Poincare.Manifold.contMDiffAt_deriv_time hRic
  have hH := contMDiffAt_hessian_scalarCurvature_fields hC F ht hX
  have hS := contMDiffAt_ricciSquare_fields hC F ht hX
  have hQ : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).ricci p.2 (X 0 p.2) (X 1 p.2) /
        (2 * (p.1 - T₀))) (t, x) :=
    hRic.div₀ (contMDiffAt_const.mul (contMDiffAt_fst.sub contMDiffAt_const))
      (mul_ne_zero (by norm_num) hτ)
  have h := ((hdRic.sub (hH.div_const 2)).add hS).add hQ
  apply h.congr_of_eventuallyEq
  have htime : ∀ᶠ p : ℝ × M in 𝓝 (t, x), p.1 ∈ interior J :=
    (continuousAt_fst : ContinuousAt Prod.fst (t, x)).eventually
      (isOpen_interior.mem_nhds ht)
  filter_upwards [htime] with p hp
  have heq := (ricci_hasDerivWithinAt_hamiltonM hC J F p.1 (interior_subset hp)
    (p.1 - T₀) p.2 (X 0 p.2) (X 1 p.2)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hp) |>.deriv
  simp only [Pi.add_apply] at ⊢
  linarith only [heq]

end Poincare.RicciFlow.Harnack
