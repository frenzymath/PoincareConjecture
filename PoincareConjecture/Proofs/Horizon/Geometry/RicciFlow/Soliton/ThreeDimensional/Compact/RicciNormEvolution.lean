import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.TensorNorm
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.RicciContraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Ricci
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private noncomputable def ricciNormPerm : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![2, 0, 3, 1] (by decide)

theorem contMDiff_ricciNormSq {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.ricciNormSq := by
  let U : CovariantTensorEvaluation n M 4 := fun y z =>
    tensorProduct D.ricciEvaluation D.ricciEvaluation y (z ∘ ricciNormPerm)
  have hU : IsSmoothCovariantTensor U :=
    (isSmoothCovariantTensor_tensorProduct hD.2.1 hD.2.1).perm ricciNormPerm
  have h := ((hU.tensorTrace (g := g)).tensorTrace (g := g)).2 Set.univ isOpen_univ
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rw [contMDiffOn_univ] at h
  convert h using 1
  ext x
  change (∑ i, ∑ j, (D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) =
    ∑ i, ∑ j, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
      D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j)
  simp only [pow_two]


theorem hasDerivAt_ricciNormSq
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    HasDerivAt (fun s => (F.connection s).ricciNormSq x)
      (D.laplacian D.ricciNormSq x -
        2 * (∑ k, ∑ i, ∑ j,
          (D.covariantTensorDerivative D.ricciEvaluation x ![b k,b i,b j]) ^ 2) +
        4 * (∑ i, ∑ j, D.ricci x (b i) (b j) *
          (∑ a, ∑ c, D.curvatureTensor x (b i) (b a) (b j) (b c) *
            D.ricci x (b a) (b c)))) t := by
  classical
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let S : ℝ → CovariantTensorEvaluation n M 2 := fun s => (F.connection s).ricciEvaluation
  let U : ℝ → CovariantTensorEvaluation n M 4 := fun s y z =>
    tensorProduct (S s) (S s) y (z ∘ ricciNormPerm)
  let V : ℝ → CovariantTensorEvaluation n M 2 := fun s => (F.metric s).tensorTrace (U s)
  have hD (s : ℝ) := hC.tensor_calculus n M (F.metric s) (F.connection s)
  have hS (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y) :
      DifferentiableAt ℝ (fun s => S s y z) t :=
    ((hC.ricci_evolution n M J F t (interior_subset ht) y (z 0) (z 1)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).differentiableAt
  have hU (s : ℝ) : IsSmoothCovariantTensor (U s) :=
    (isSmoothCovariantTensor_tensorProduct (hD s).2.1 (hD s).2.1).perm ricciNormPerm
  have hUt (y : M) (z : Fin 4 → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s => U s y z) (deriv (fun s => U s y z) t) t :=
    ((hS y _).mul (hS y _)).hasDerivAt
  have hV (s : ℝ) : IsSmoothCovariantTensor (V s) := (hU s).tensorTrace
  have hVt (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s => V s y z) (deriv (fun s => V s y z) t) t :=
    (F.hasDerivAt_tensorTrace (W := fun s y z => deriv (fun r => U r y z) s)
      ht y hU (hUt y) z).differentiableAt.hasDerivAt
  have hnorm (s : ℝ) (y : M) :
      (∑ i, V s y ![(F.metric s).orthonormalBasis y i,
        (F.metric s).orthonormalBasis y i]) = (F.connection s).ricciNormSq y := by
    change (∑ i, ∑ j, (F.connection s).ricci y
      ((F.metric s).orthonormalBasis y i) ((F.metric s).orthonormalBasis y j) *
        (F.connection s).ricci y ((F.metric s).orthonormalBasis y i)
          ((F.metric s).orthonormalBasis y j)) = _
    simp only [LeviCivitaData.ricciNormSq, pow_two]
  have htime := F.hasDerivAt_tensorTrace (W := fun s y z => deriv (fun r => V r y z) s)
    ht x hV (hVt x) Fin.elim0
  have htime' : DifferentiableAt ℝ (fun s => (F.connection s).ricciNormSq x) t := by
    have hfn : (fun s => (F.metric s).tensorTrace (V s) x Fin.elim0) =
        (fun s => (F.connection s).ricciNormSq x) := funext fun s => hnorm s x
    rw [← hfn]
    exact htime.differentiableAt
  have heq := F.scalarHeatOperator_tensorTrace_two hC ht hV
    (W := fun s y z => deriv (fun r => V r y z) s) hVt x
  simp only [hnorm] at heq
  have hheat (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      F.tensorHeatOperator U t x ![b j,b j,b i,b i] =
        4 * D.ricci x (b i) (b j) *
          (∑ a, ∑ c, D.curvatureTensor x (b i) (b a) (b j) (b c) *
            D.ricci x (b a) (b c)) -
        2 * ∑ k, (D.covariantTensorDerivative D.ricciEvaluation x ![b k,b i,b j]) ^ 2 := by
    change F.tensorHeatOperator
      (fun s y z => tensorProduct (S s) (S s) y (z ∘ ricciNormPerm)) t x _ = _
    rw [F.tensorHeatOperator_reindex]
    have hv : ![b j,b j,b i,b i] ∘ ricciNormPerm = ![b i,b j,b i,b j] := by
      ext k; fin_cases k <;> rfl
    rw [hv, F.tensorHeatOperator_tensorProduct_two_two (hD t).2.1 (hD t).2.1
      ((hD t).2.2.1 _ _ (hD t).2.1) ((hD t).2.2.1 _ _ (hD t).2.1) hS hS]
    dsimp only [S]
    rw [F.tensorHeatOperator_ricci hC ht]
    simp only [LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one,
      ← pow_two]
    dsimp only [D, b]
    ring
  have htrace (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      F.tensorHeatOperator V t x ![b i,b i] =
        ∑ j, F.tensorHeatOperator U t x ![b j,b j,b i,b i] :=
    F.tensorHeatOperator_tensorTrace_four hC ht hU
      (W := fun s y z => deriv (fun r => U r y z) s) hUt x (b i) (b i)
  change _ = ∑ i, F.tensorHeatOperator V t x ![b i,b i] at heq
  simp_rw [htrace, hheat] at heq
  have hsum : (∑ i, ∑ j, ∑ k,
      (D.covariantTensorDerivative D.ricciEvaluation x ![b k,b i,b j]) ^ 2) =
      ∑ k, ∑ i, ∑ j,
        (D.covariantTensorDerivative D.ricciEvaluation x ![b k,b i,b j]) ^ 2 := by
    calc
      _ = ∑ i, ∑ k, ∑ j,
          (D.covariantTensorDerivative D.ricciEvaluation x ![b k,b i,b j]) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hsum] at heq
  apply htime'.hasDerivAt.congr_deriv
  dsimp only [D, b] at heq
  linarith only [heq]



theorem normalizedRicciNormSq_heat_equation
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J)
    (hR : ∀ y : M, 0 < (F.connection t).scalarCurvature y) (x : M) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let q := fun s y => (F.connection s).ricciNormSq y / (F.connection s).scalarCurvature y ^ 2
    deriv (fun s => q s x) t = D.laplacian (q t) x +
      (2 / D.scalarCurvature x ^ 2) *
        (F.metric t).inner x (D.gradient (q t) x)
          (D.gradient (fun y => D.scalarCurvature y ^ 2) x) +
      (-2 * (∑ k, ∑ i, ∑ j,
        (D.covariantTensorDerivative D.ricciEvaluation x ![b k,b i,b j]) ^ 2) +
        4 * (∑ i, ∑ j, D.ricci x (b i) (b j) *
          (∑ a, ∑ c, D.curvatureTensor x (b i) (b a) (b j) (b c) *
            D.ricci x (b a) (b c))) -
        4 * q t x * D.scalarCurvature x * D.ricciNormSq x +
        2 * q t x * (F.metric t).inner x
          (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x)) /
        D.scalarCurvature x ^ 2 := by
  let D := F.connection t
  let q := fun s y => (F.connection s).ricciNormSq y / (F.connection s).scalarCurvature y ^ 2
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hRs := hD.contMDiff_scalarCurvature
  have hSs := contMDiff_ricciNormSq D hD
  have hqs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q t) :=
    hSs.div₀ (hRs.pow 2) (fun y => pow_ne_zero _ (hR y).ne')
  have hdR := (hC.scalar_evolution n M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have hdS := F.hasDerivAt_ricciNormSq hC ht x
  dsimp only at hdS
  have hdq := hdS.div (hdR.pow 2) (pow_ne_zero 2 (hR x).ne')
  change HasDerivAt (fun s => q s x) _ t at hdq
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hdq
  have hprod : (fun y => q t y * D.scalarCurvature y ^ 2) = D.ricciNormSq := by
    funext y
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (hR y).ne')
  have hL := D.laplacian_mul hqs (hRs.pow 2) x
  rw [hprod, D.laplacian_sq hRs] at hL
  change deriv (fun s => q s x) t = _
  rw [hdq.deriv]
  dsimp only [D] at hL ⊢
  rw [hL]
  dsimp only [q]
  field_simp [(hR x).ne']
  ring

end PoincareConjecture.RicciFlow
