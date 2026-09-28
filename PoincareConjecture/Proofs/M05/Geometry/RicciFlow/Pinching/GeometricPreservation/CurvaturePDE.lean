import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.TensorConnection
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.CurvatureReaction
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Laplacian.Product
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.LaplacianTrace.Four
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.LaplacianRegularity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Scaling

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Geometry.Curvature.Operator Poincare.HamiltonIvey

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem smooth_metricTensor :
    IsSmoothCovariantTensor (fun (x : M) (v : Fin 2 → TangentSpace (𝓡 n) x) =>
      g.inner x (v 0) (v 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  constructor
  · intro x
    refine ⟨TensorFiber.toMultilinear (TensorFiber.operatorTensor
      (LinearMap.id : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x)), ?_⟩
    intro v
    rfl
  · intro U hU X hX
    exact (hX 0).inner_bundle (hX 1)

private theorem covariantTensorDerivative_product_metric (D : LeviCivitaData g)
    {k : ℕ} {S : CovariantTensorEvaluation n M k} (hS : IsSmoothCovariantTensor S) :
    D.covariantTensorDerivative
        (tensorProduct S (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
          g.inner x (v 0) (v 1))) =
      tensorProduct (D.covariantTensorDerivative S)
        (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) => g.inner x (v 0) (v 1)) := by
  funext x v
  have hv : v = Fin.cons (v 0) (fun i => v i.succ) := by
    ext i
    cases i using Fin.cases <;> rfl
  rw [hv, D.covariantTensorDerivative_tensorProduct hS (smooth_metricTensor (g := g))]
  have hz := D.covariantTensorDerivative_metric_eq_zero x (v 0)
    (v (Fin.natAdd k 0).succ) (v (Fin.natAdd k 1).succ)
  have htuple : Fin.cons (v 0) (fun j : Fin 2 => v (Fin.natAdd k j).succ) =
      ![v 0, v (Fin.natAdd k 0).succ, v (Fin.natAdd k 1).succ] := by
    ext j
    fin_cases j <;> rfl
  simp only [htuple, hz, mul_zero, add_zero, tensorProduct]
  congr 1

private theorem tensorLaplacian_scalar_metric (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y w => f y * g.inner y (w 0) (w 1)) x ![u, v] =
      D.laplacian f x * g.inner x u v := by
  let S : CovariantTensorEvaluation n M 0 := fun y _ => f y
  have hS : IsSmoothCovariantTensor S := by
    constructor
    · intro y
      exact ⟨MultilinearMap.constOfIsEmpty ℝ _ (f y), fun _ => rfl⟩
    · intro U hU X hX
      exact hf.contMDiffOn
  have hfirst := covariantTensorDerivative_product_metric D hS
  have hsecond := covariantTensorDerivative_product_metric D
    (D.covariantTensorDerivative_isSmooth hS)
  have heq : (fun y (w : Fin 2 → TangentSpace (𝓡 n) y) =>
      f y * g.inner y (w 0) (w 1)) =
      tensorProduct S (fun y (w : Fin 2 → TangentSpace (𝓡 n) y) =>
        g.inner y (w 0) (w 1)) := by
    funext y w
    rfl
  rw [heq]
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative, hfirst, hsecond]
  change (∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative S) x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i] * g.inner x u v) = _
  rw [← Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [covariantTensorDerivative, hessian, hessianOnFields, S]

private theorem tensorLaplacian_ricciComplement_split (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian D.ricciComplementEvaluation x ![u, v] =
      (D.laplacian D.scalarCurvature x / 2) * g.inner x u v -
        D.tensorLaplacian D.ricciEvaluation x ![u, v] := by
  have hscalar : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ D.scalarCurvature := by
    change ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun y => ∑ i, D.ricci y (g.orthonormalBasis y i) (g.orthonormalBasis y i))
    have hs := (hD.2.1.tensorTrace (g := g)).2 Set.univ isOpen_univ
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    simpa [contMDiffOn_univ, RiemannianMetric.tensorTrace, scalarCurvature,
      ricciEvaluation] using hs
  let S : CovariantTensorEvaluation n M 2 := fun y w =>
    (D.scalarCurvature y / 2) * g.inner y (w 0) (w 1)
  have hS : IsSmoothCovariantTensor S := by
    have hh := (D.isSmoothCovariantTensor_ricciComplementEvaluation hD).add hD.2.1
    convert hh using 1
    funext y w
    simp only [S, ricciComplementEvaluation, ricciEvaluation, sub_add_cancel]
  change D.tensorLaplacian (fun y w => S y w - D.ricciEvaluation y w) x ![u, v] = _
  rw [D.tensorLaplacian_sub hS hD.2.1 (D.covariantTensorDerivative_isSmooth hS)
    (D.covariantTensorDerivative_isSmooth hD.2.1)]
  change D.tensorLaplacian S x ![u, v] - _ = _
  rw [tensorLaplacian_scalar_metric D (hscalar.div_const 2)]
  have hf : (fun y => D.scalarCurvature y / 2) =
      fun y => (1 / 2 : ℝ) * D.scalarCurvature y := by
    funext y
    ring
  rw [hf, D.laplacian_const_mul]
  ring

private theorem tensorLaplacian_ricci_eq_sum_orthonormalBasis
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) x))
      (u v : TangentSpace (𝓡 n) x),
      D.tensorLaplacian D.ricciEvaluation x ![u, v] =
        ∑ i, D.tensorLaplacian D.riemannEvaluation x ![u, e i, v, e i] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro e u v
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2, 0, 3, 1] (by decide)
  let T : CovariantTensorEvaluation n M 4 := fun y w => D.riemannEvaluation y (w ∘ σ)
  have hT : IsSmoothCovariantTensor T := hD.1.perm σ
  have htrace : D.ricciEvaluation = g.tensorTrace T := by
    funext y w
    rfl
  rw [htrace, D.tensorLaplacian_tensorTrace_four hT (D.covariantTensorDerivative_isSmooth hT)]
  have hperm (p q : TangentSpace (𝓡 n) x) :
      ![p, q, u, v] ∘ σ = ![u, p, v, q] := by
    ext i
    fin_cases i <;> rfl
  change (∑ i, D.tensorLaplacian T x
    ![g.orthonormalBasis x i, g.orthonormalBasis x i, u, v]) = _
  simp only [T, D.tensorLaplacian_reindex, hperm]
  obtain ⟨A, hA⟩ := D.tensorLaplacian_multilinear hD.1 x
  let C := ((A.domDomCongr (Equiv.swap (1 : Fin 4) 2)).curryLeft u).curryLeft v
  have hC (p q : TangentSpace (𝓡 n) x) : C ![p, q] =
      D.tensorLaplacian D.riemannEvaluation x ![u, p, v, q] := by
    rw [hA]
    change A ((Fin.cons u (Fin.cons v ![p, q])) ∘ Equiv.swap 1 2) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  simp_rw [← hC]
  exact bilinear_sum_orthonormalBasis_eq (bilinearOfTwoTensor C) (g.orthonormalBasis x) e

private theorem tensorLaplacian_riemann_skew_last
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian D.riemannEvaluation x ![u, v, w, z] =
      -D.tensorLaplacian D.riemannEvaluation x ![u, v, z, w] := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
  have heq : (fun y r => D.riemannEvaluation y (r ∘ σ)) =
      (fun y r => (-1 : ℝ) * D.riemannEvaluation y r) := by
    funext y r
    simpa [riemannEvaluation, σ, Equiv.swap_apply_def] using
      (hD.2.2.2.1 y (r 0) (r 1) (r 3) (r 2)).1
  have h := congrArg (fun T => D.tensorLaplacian T x ![u, v, z, w]) heq
  rw [D.tensorLaplacian_reindex, D.tensorLaplacian_const_mul hD.1
    (D.covariantTensorDerivative_isSmooth hD.1)] at h
  have hv : ![u, v, z, w] ∘ σ = ![u, v, w, z] := by
    ext i
    fin_cases i <;> rfl
  simpa only [hv, neg_one_mul] using h

private theorem tensorLaplacian_riemann_pair
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian D.riemannEvaluation x ![u, v, w, z] =
      D.tensorLaplacian D.riemannEvaluation x ![w, z, u, v] := by
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2, 3, 0, 1] (by decide)
  have heq : (fun y r => D.riemannEvaluation y (r ∘ σ)) = D.riemannEvaluation := by
    funext y r
    exact (hD.2.2.2.1 y (r 2) (r 3) (r 0) (r 1)).2.1
  have h := congrArg (fun T => D.tensorLaplacian T x ![w, z, u, v]) heq
  rw [D.tensorLaplacian_reindex] at h
  have hv : ![w, z, u, v] ∘ σ = ![u, v, w, z] := by
    ext i
    fin_cases i <;> rfl
  exact hv ▸ h

private theorem cyclic_eq_half_double_trace_sub_ricci
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (hpair : ∀ i j k l, R i j k l = R k l i j) (i j : Fin 3) :
    ((∑ p, ∑ q, R p q p q) / 2) * (if i = j then 1 else 0) -
        ∑ p, R i p j p =
      R (pairFirst i) (pairSecond i) (pairFirst j) (pairSecond j) := by
  have hdiagFirst (i k l) : R i i k l = 0 := by linarith [hfirst i i k l]
  have hdiagLast (i j k) : R i j k k = 0 := by linarith [hlast i j k k]
  have hswap (i j) : R i j i j = R j i j i := by
    rw [hfirst, hlast j i i j, neg_neg]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, pairFirst, pairSecond, hdiagFirst, hdiagLast]
  · linarith [hswap 0 1, hswap 0 2, hswap 1 2]
  · linarith [hfirst 0 2 1 2, hpair 2 0 1 2]
  · linarith [hlast 0 1 2 1, hpair 0 1 1 2]
  · linarith [hlast 1 2 0 2, hpair 1 2 2 0]
  · linarith [hswap 0 1, hswap 0 2, hswap 1 2]
  · linarith [hfirst 1 0 2 0, hpair 0 1 2 0]
  · linarith [hfirst 2 1 0 1, hpair 1 2 0 1]
  · linarith [hlast 2 0 1 0, hpair 2 0 0 1]
  · linarith [hswap 0 1, hswap 0 2, hswap 1 2]

theorem tensorLaplacian_ricciComplement_apply_orthonormalBasis
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) (i j : Fin 3),
      D.tensorLaplacian D.ricciComplementEvaluation x ![e i, e j] =
        D.tensorLaplacian D.riemannEvaluation x
          ![e (pairFirst i), e (pairSecond i), e (pairFirst j), e (pairSecond j)] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro e i j
  let R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun p q r s =>
    D.tensorLaplacian D.riemannEvaluation x ![e p, e q, e r, e s]
  have hscalar : D.laplacian D.scalarCurvature x = ∑ p, ∑ q, R p q p q := by
    rw [← D.sum_tensorLaplacian_ricci_eq_laplacian_scalar hD x]
    obtain ⟨A, hA⟩ := D.tensorLaplacian_multilinear hD.2.1 x
    have h := bilinear_sum_orthonormalBasis_eq (bilinearOfTwoTensor A)
      (g.orthonormalBasis x) e
    simp only [bilinearOfTwoTensor_apply, ← hA] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro p _
    exact tensorLaplacian_ricci_eq_sum_orthonormalBasis D hD x e (e p) (e p)
  rw [tensorLaplacian_ricciComplement_split D hD]
  change (_ / 2) * inner ℝ (e i) (e j) - _ = _
  rw [e.inner_eq_ite, hscalar,
    tensorLaplacian_ricci_eq_sum_orthonormalBasis D hD x e]
  apply cyclic_eq_half_double_trace_sub_ricci R _ _ _ i j
  · intro p q r s
    change D.tensorLaplacian D.riemannEvaluation x ![e p, e q, e r, e s] = _
    rw [tensorLaplacian_riemann_pair D hD,
      tensorLaplacian_riemann_skew_last D hD,
      tensorLaplacian_riemann_pair D hD x (e r) (e s) (e q) (e p)]
  · intro p q r s
    exact tensorLaplacian_riemann_skew_last D hD x (e p) (e q) (e r) (e s)
  · intro p q r s
    exact tensorLaplacian_riemann_pair D hD x (e p) (e q) (e r) (e s)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow.Frame

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

private theorem exists_canonicalTransport_orthonormalBasis
    (F : RicciFlow 3 M (Ico a b)) (hab : a < b)
    {t : ℝ} (ht : t ∈ Ico a b) (x : M)
    (e : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (he : ∀ i j, (F.metric a).inner x (e i) (e j) = if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ∃ q : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
      ∀ i, q i = canonicalTransport F t x (e i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let c := e.map (orthonormalTransport F t x).toLinearEquiv
  have hc : Orthonormal ℝ c := by
    rw [orthonormal_iff_ite]
    intro i j
    change (F.metric t).inner x (canonicalTransport F t x (e i))
      (canonicalTransport F t x (e j)) = _
    rw [canonicalTransport_pairing F hab ht, he]
  exact ⟨c.toOrthonormalBasis hc, fun i => by
    rw [Module.Basis.coe_toOrthonormalBasis]
    rfl⟩

theorem transportPullback_ricciComplement_eq_cyclic [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Ico a b))
    (hab : a < b) {t : ℝ} (ht : t ∈ Ico a b) (x : M)
    (e : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (he : ∀ i j, (F.metric a).inner x (e i) (e j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    transportPullbackTensor F t (F.connection t).ricciComplementEvaluation x ![e i, e j] =
      (F.connection t).curvatureTensor x
        (canonicalTransport F t x (e (pairFirst i)))
        (canonicalTransport F t x (e (pairSecond i)))
        (canonicalTransport F t x (e (pairFirst j)))
        (canonicalTransport F t x (e (pairSecond j))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  obtain ⟨q, hq⟩ := exists_canonicalTransport_orthonormalBasis F hab ht x e he
  have h := (F.connection t).ricciComplementTensor_apply_orthonormalBasis
    (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x q i j
  simp only [LeviCivitaData.ricciComplementTensor_apply, curvatureMatrix, hq] at h
  convert h using 1
  rfl

theorem canonicalTransport_hasDerivAt_ricciComplement_cyclic [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Ico a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M)
    (e : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (he : ∀ i j, (F.metric a).inner x (e i) (e j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt
      (fun s => transportPullbackTensor F s (F.connection s).ricciComplementEvaluation x
        ![e i, e j])
      (transportedTensorLaplacian F ⟨ht.1.le, ht.2⟩
          (transportPullbackTensor F t (F.connection t).riemannEvaluation) x
          ![e (pairFirst i), e (pairSecond i), e (pairFirst j), e (pairSecond j)] +
        tensorReaction ((F.connection t).ricciComplementTensor
          (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x)
          ![canonicalTransport F t x (e i), canonicalTransport F t x (e j)]) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have hab : a < b := ht.1.trans ht.2
  obtain ⟨q, hq⟩ := exists_canonicalTransport_orthonormalBasis
    F hab ⟨ht.1.le, ht.2⟩ x e he
  have hr := (F.connection t).tensorReaction_ricciComplementTensor_eq_curvatureB
    (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x q i j
  simp only [hq] at hr
  rw [hr]
  apply (canonicalTransport_curvature_pde_on_initial_tensor hC F ht x
    (e (pairFirst i)) (e (pairSecond i)) (e (pairFirst j))
    (e (pairSecond j))).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact transportPullback_ricciComplement_eq_cyclic hC F hab ⟨hs.1.le, hs.2⟩ x e he i j

theorem canonicalTransport_hasDerivAt_ricciComplement [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Ico a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M)
    (e : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (he : ∀ i j, (F.metric a).inner x (e i) (e j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt
      (fun s => transportPullbackTensor F s (F.connection s).ricciComplementEvaluation x
        ![e i, e j])
      (transportedTensorLaplacian F ⟨ht.1.le, ht.2⟩
          (transportPullbackTensor F t (F.connection t).ricciComplementEvaluation) x ![e i, e j] +
        tensorReaction ((F.connection t).ricciComplementTensor
          (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x)
          ![canonicalTransport F t x (e i), canonicalTransport F t x (e j)]) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have hab : a < b := ht.1.trans ht.2
  have hD := hC.tensor_calculus 3 M (F.metric t) (F.connection t)
  obtain ⟨q, hq⟩ := exists_canonicalTransport_orthonormalBasis
    F hab ⟨ht.1.le, ht.2⟩ x e he
  have hl := (F.connection t).tensorLaplacian_ricciComplement_apply_orthonormalBasis
    hD x q i j
  simp only [hq] at hl
  have h := canonicalTransport_hasDerivAt_ricciComplement_cyclic hC F ht x e he i j
  rw [transportedTensorLaplacian_pullback F ⟨ht.1.le, ht.2⟩ hD.1] at h
  rw [transportedTensorLaplacian_pullback F ⟨ht.1.le, ht.2⟩
    ((F.connection t).isSmoothCovariantTensor_ricciComplementEvaluation hD)]
  have hv2 : (fun l => canonicalTransport F t x (![e i, e j] l)) =
      ![canonicalTransport F t x (e i), canonicalTransport F t x (e j)] := by
    ext l
    fin_cases l <;> rfl
  have hv4 : (fun l => canonicalTransport F t x
      (![e (pairFirst i), e (pairSecond i), e (pairFirst j), e (pairSecond j)] l)) =
      ![canonicalTransport F t x (e (pairFirst i)),
        canonicalTransport F t x (e (pairSecond i)),
        canonicalTransport F t x (e (pairFirst j)),
        canonicalTransport F t x (e (pairSecond j))] := by
    ext l
    fin_cases l <;> rfl
  simp only [transportPullbackTensor, hv2, hv4] at h ⊢
  rw [hl]
  exact h

end PoincareConjecture.RicciFlow.Frame
