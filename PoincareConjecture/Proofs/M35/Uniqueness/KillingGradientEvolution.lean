import PoincareConjecture.Proofs.M35.Uniqueness.KillingCovectorHeat
import PoincareConjecture.Proofs.M35.Uniqueness.KillingRicciCovector
import PoincareConjecture.Proofs.M04.TensorLaplacianCommutator
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity










set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

private theorem scalarDerivative_congr {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {f h : M → ℝ} {x : M}
    (he : f =ᶠ[𝓝 x] h) : mvfderiv (𝓡 n) f x = mvfderiv (𝓡 n) h x := by
  unfold mvfderiv
  rw [he.mfderiv_eq, he.eq_of_nhds]

theorem covariantTensorDerivative_eq_of_eventuallyEq {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} {S T : CovariantTensorEvaluation n M k} {x : M}
    (h : ∀ᶠ y in 𝓝 x, S y = T y) (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative S x v = D.covariantTensorDerivative T x v := by
  have he : (fun y => S y (fun i => FiberBundle.extend
      (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) =ᶠ[𝓝 x]
      (fun y => T y (fun i => FiberBundle.extend
        (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) :=
    h.mono (fun y hy => congrFun hy _)
  simp only [LeviCivitaData.covariantTensorDerivative,
    scalarDerivative_congr he, h.self_of_nhds]

private theorem derivative_sub {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (a : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w => S y w - T y w) x (Fin.cons a v) =
      D.covariantTensorDerivative S x (Fin.cons a v) -
        D.covariantTensorDerivative T x (Fin.cons a v) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let V := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)
  have hV (i) := M04.contMDiffOn_extend_baseSet (v i)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hs := ((hS.2 e.baseSet e.open_baseSet V hV).contMDiffAt
    (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have ht := ((hT.2 e.baseSet e.open_baseSet V hV).contMDiffAt
    (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  dsimp only [V] at hs ht
  simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ,
    mvfderiv_fun_sub hs ht, sub_apply, Finset.sum_sub_distrib]
  ring




theorem killingCovectorGradient_heat_hasDerivAt_of_eventually_heat
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ioo 0 G.lifetime)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ))
    (x a b : StandardCapSpace)
    (hheat : ∀ᶠ y in 𝓝 x, HasDerivWithinAt (fun s => X s y)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) y
          ((G.flow.metric t).orthonormalBasis y i)
          ((G.flow.metric t).orthonormalBasis y i))
        (RicciFlow.ricciSharp (G.flow.connection t) y (X t y))) (Ico 0 G.lifetime) t) :
    let D := G.flow.connection t
    let e := (G.flow.metric t).orthonormalBasis x
    let A := fun s => killingCovector (G.flow.metric s) (X s)
    let K := D.covariantTensorDerivative (A t)
    HasDerivAt (fun s => (G.flow.connection s).covariantTensorDerivative (A s) x ![a, b])
      (D.tensorLaplacian K x ![a, b] -
        (∑ q, D.ricci x a (e q) * K x ![e q, b]) -
        (∑ q, D.ricci x b (e q) * K x ![a, e q]) -
        2 * (∑ p, ∑ q, D.curvatureTensor x a (e p) (e q) b * K x ![e p, e q])) t := by
  classical
  let D := G.flow.connection t
  let e := (G.flow.metric t).orthonormalBasis x
  let A := fun s => killingCovector (G.flow.metric s) (X s)
  let K := D.covariantTensorDerivative (A t)
  let S := D.covariantTensorDerivative D.ricciEvaluation x
  have hA (s) : IsSmoothCovariantTensor (A s) :=
    isSmoothCovariantTensor_killingCovector _ _ (hX s)
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow
    (K := Ioo 0 G.lifetime) Ioo_subset_Ico_self ordConnected_Ioo
    (show (Ioo 0 G.lifetime).Nontrivial from
      ⟨t / 2, ⟨by linarith only [ht.1], by linarith only [ht.1, ht.2]⟩,
        t, ht, by linarith only [ht.1]⟩)
  have hti : t ∈ interior (Ioo 0 G.lifetime) := by simpa only [interior_Ioo] using ht
  have hd := M04.hasDerivAt_covariantTensorDerivative F hA
    (killingCovector_joint_flow F X hJoint) hti x a ![b]
  have hs : ∀ᶠ y in 𝓝 x, (fun w => deriv (fun s => A s y w) t) =
      (fun w => D.tensorLaplacian (A t) y w - killingRicciCovector D (X t) y w) := by
    filter_upwards [hheat] with y hy
    funext w
    exact (killingCovector_heat_hasDerivAt G ht X (hX t) y w hy).deriv
  dsimp only [F, Poincare.Geometry.RicciFlow.Harnack.restrictFlow] at hd
  rw [covariantTensorDerivative_eq_of_eventuallyEq (G.flow.connection t) hs] at hd
  have hsub := derivative_sub D (M04.isSmoothCovariantTensor_tensorLaplacian D (hA t))
    (isSmoothCovariantTensor_killingRicciCovector D (X t) (hX t)) x a ![b]
  dsimp only [D] at hsub hd
  rw [hsub] at hd
  simp only [Fin.sum_univ_one] at hd
  change HasDerivAt (fun s => (G.flow.connection s).covariantTensorDerivative (A s)
    x ![a, b]) (D.covariantTensorDerivative (D.tensorLaplacian (A t)) x ![a, b] -
      D.covariantTensorDerivative (killingRicciCovector D (X t)) x ![a, b] +
        ∑ q, (S ![a, b, e q] + S ![b, a, e q] - S ![e q, a, b]) *
          A t x ![e q]) t at hd
  have hc := M04.covariantTensorDerivative_tensorLaplacian_commutator D (hA t) x a ![b]
  simp only [Fin.sum_univ_one] at hc
  change D.covariantTensorDerivative (D.tensorLaplacian (A t)) x ![a, b] -
      D.tensorLaplacian K x ![a, b] =
    -(∑ p, ∑ q, D.curvatureTensor x a (e p) (e q) (e p) * K x ![e q, b]) -
      2 * (∑ p, ∑ q, D.curvatureTensor x a (e p) (e q) b * K x ![e p, e q]) -
      (∑ p, ∑ q, D.covariantTensorDerivative D.riemannEvaluation x
        ![e p, a, e p, e q, b] * A t x ![e q]) at hc
  have htrace : (∑ p, ∑ q,
      D.curvatureTensor x a (e p) (e q) (e p) * K x ![e q, b]) =
      ∑ q, D.ricci x a (e q) * K x ![e q, b] := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_mul]
    rfl
  have hdiv : (∑ p, ∑ q, D.covariantTensorDerivative D.riemannEvaluation x
      ![e p, a, e p, e q, b] * A t x ![e q]) =
      ∑ q, (S ![b, a, e q] - S ![e q, a, b]) * A t x ![e q] := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_mul, killing_riemannDerivative_divergence]
    congr 1
    dsimp only [S]
    rw [M04.ricci_covariantDerivative_symm D x b (e q) a,
      M04.ricci_covariantDerivative_symm D x (e q) b a]
  have hRic := killingRicciCovector_derivative_frame D (X t) (hX t) x a b
  change D.covariantTensorDerivative (killingRicciCovector D (X t)) x ![a, b] =
    (∑ q, S ![a, b, e q] * A t x ![e q]) +
      (∑ q, D.ricci x b (e q) * K x ![a, e q]) at hRic
  rw [htrace, hdiv] at hc
  have hsplit :
      (∑ q, (S ![a, b, e q] + S ![b, a, e q] - S ![e q, a, b]) * A t x ![e q]) =
      (∑ q, S ![a, b, e q] * A t x ![e q]) +
        (∑ q, (S ![b, a, e q] - S ![e q, a, b]) * A t x ![e q]) := by
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  apply hd.congr_deriv
  rw [hRic, hsplit]
  linarith only [hc]


theorem killingCovectorGradient_heat_hasDerivAt
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ioo 0 G.lifetime)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ico 0 G.lifetime ×ˢ univ))
    (hheat : ∀ x, HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Ico 0 G.lifetime) t)
    (x a b : StandardCapSpace) :
    let D := G.flow.connection t
    let e := (G.flow.metric t).orthonormalBasis x
    let A := fun s => killingCovector (G.flow.metric s) (X s)
    let K := D.covariantTensorDerivative (A t)
    HasDerivAt (fun s => (G.flow.connection s).covariantTensorDerivative (A s) x ![a, b])
      (D.tensorLaplacian K x ![a, b] -
        (∑ q, D.ricci x a (e q) * K x ![e q, b]) -
        (∑ q, D.ricci x b (e q) * K x ![a, e q]) -
        2 * (∑ p, ∑ q, D.curvatureTensor x a (e p) (e q) b * K x ![e p, e q])) t :=
  killingCovectorGradient_heat_hasDerivAt_of_eventually_heat G ht X hX
    (hJoint.mono (prod_mono Ioo_subset_Ico_self Subset.rfl)) x a b
    (Filter.Eventually.of_forall hheat)

end PoincareConjecture.M35.Uniqueness
