import PoincareConjecture.Proofs.M35.Uniqueness.KillingGradientEvolution
import PoincareConjecture.Proofs.M35.Uniqueness.KillingDefectTensor
import PoincareConjecture.Proofs.M35.Uniqueness.LichnerowiczEnergy










set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness



theorem killingDefectTensor_heat_hasDerivAt_of_eventually_heat
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ioo 0 G.lifetime)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ))
    (x : StandardCapSpace)
    (hheat : ∀ᶠ y in 𝓝 x, HasDerivWithinAt (fun s => X s y)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) y
          ((G.flow.metric t).orthonormalBasis y i)
          ((G.flow.metric t).orthonormalBasis y i))
        (RicciFlow.ricciSharp (G.flow.connection t) y (X t y))) (Ico 0 G.lifetime) t)
    (v : Fin 2 → StandardCapSpace) :
    let H := fun s => killingDefectTensor (G.flow.connection s) (X s)
    HasDerivAt (fun s => H s x v)
      ((G.flow.connection t).tensorLaplacian (H t) x v +
        lichnerowiczReaction (G.flow.connection t) (H t) x v) t := by
  classical
  let D := G.flow.connection t
  let e := (G.flow.metric t).orthonormalBasis x
  let A := fun s => killingCovector (G.flow.metric s) (X s)
  let K := D.covariantTensorDerivative (A t)
  let H := fun s => killingDefectTensor (G.flow.connection s) (X s)
  let a := v 0
  let b := v 1
  have hv : ![a, b] = v := by ext i; fin_cases i <;> rfl
  have hdab := killingCovectorGradient_heat_hasDerivAt_of_eventually_heat G ht X hX
    hJoint x a b hheat
  have hdba := killingCovectorGradient_heat_hasDerivAt_of_eventually_heat G ht X hX
    hJoint x b a hheat
  have hfun : (fun s => H s x v) = fun s =>
      (G.flow.connection s).covariantTensorDerivative (A s) x ![a, b] +
        (G.flow.connection s).covariantTensorDerivative (A s) x ![b, a] := by
    funext s
    exact killing_defect_eq_covector_symmetrization (G.flow.connection s) (X s) (hX s) x a b
  change HasDerivAt (fun s => H s x v)
    (D.tensorLaplacian (H t) x v + lichnerowiczReaction D (H t) x v) t
  rw [hfun]
  apply (hdab.add hdba).congr_deriv
  have hH (u w : StandardCapSpace) : H t x ![u, w] = K x ![u, w] + K x ![w, u] :=
    killing_defect_eq_covector_symmetrization D (X t) (hX t) x u w
  have hfirst : (∑ p, ∑ q, D.curvatureTensor x a (e p) (e q) b * K x ![e p, e q]) =
      -(∑ p, ∑ q, D.curvatureTensor x a (e p) b (e q) * K x ![e p, e q]) := by
    simp_rw [M04.curvatureTensor_swap_last D x a _ _ b]
    simp only [neg_mul, Finset.sum_neg_distrib]
  have hsecond : (∑ p, ∑ q, D.curvatureTensor x b (e p) (e q) a * K x ![e p, e q]) =
      -(∑ p, ∑ q, D.curvatureTensor x a (e p) b (e q) * K x ![e q, e p]) := by
    simp_rw [M04.curvatureTensor_swap_last D x b _ _ a,
      M04.curvatureTensor_pair_exchange D x b _ a _]
    simp only [neg_mul, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
  have hreaction : lichnerowiczReaction D (H t) x ![a, b] =
      2 * ((∑ p, ∑ q, D.curvatureTensor x a (e p) b (e q) * K x ![e p, e q]) +
        (∑ p, ∑ q, D.curvatureTensor x a (e p) b (e q) * K x ![e q, e p])) -
      ((∑ q, D.ricci x a (e q) * K x ![e q, b]) +
        (∑ q, D.ricci x a (e q) * K x ![b, e q])) -
      ((∑ q, D.ricci x b (e q) * K x ![a, e q]) +
        (∑ q, D.ricci x b (e q) * K x ![e q, a])) := by
    have hu0 (q) : Function.update ![a, b] (0 : Fin 2) (e q) = ![e q, b] := by
      ext i
      fin_cases i <;> simp
    have hu1 (q) : Function.update ![a, b] (1 : Fin 2) (e q) = ![a, e q] := by
      ext i
      fin_cases i <;> simp
    change 2 * (∑ p, ∑ q, D.curvatureTensor x a (e p) b (e q) * H t x ![e p, e q]) -
      (∑ j : Fin 2, ∑ q, D.ricci x (![a, b] j) (e q) *
        H t x (Function.update ![a, b] j (e q))) = _
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1, hH,
      mul_add, Finset.sum_add_distrib]
    ring
  have hlap := killingDefectTensor_laplacian D (X t) (hX t) x a b
  change D.tensorLaplacian (H t) x ![a, b] =
    D.tensorLaplacian K x ![a, b] + D.tensorLaplacian K x ![b, a] at hlap
  change (D.tensorLaplacian K x ![a, b] -
    (∑ q, D.ricci x a (e q) * K x ![e q, b]) -
    (∑ q, D.ricci x b (e q) * K x ![a, e q]) -
    2 * (∑ p, ∑ q, D.curvatureTensor x a (e p) (e q) b * K x ![e p, e q])) +
    (D.tensorLaplacian K x ![b, a] -
      (∑ q, D.ricci x b (e q) * K x ![e q, a]) -
      (∑ q, D.ricci x a (e q) * K x ![b, e q]) -
      2 * (∑ p, ∑ q, D.curvatureTensor x b (e p) (e q) a * K x ![e p, e q])) =
    D.tensorLaplacian (H t) x v + lichnerowiczReaction D (H t) x v
  rw [← hv, hlap, hreaction, hfirst, hsecond]
  ring

theorem killingDefectTensor_heat_hasDerivAt_positive
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ioo 0 G.lifetime)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ))
    (hheat : ∀ x, HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Ico 0 G.lifetime) t)
    (x : StandardCapSpace) (v : Fin 2 → StandardCapSpace) :
    let H := fun s => killingDefectTensor (G.flow.connection s) (X s)
    HasDerivAt (fun s => H s x v)
      ((G.flow.connection t).tensorLaplacian (H t) x v +
        lichnerowiczReaction (G.flow.connection t) (H t) x v) t :=
  killingDefectTensor_heat_hasDerivAt_of_eventually_heat G ht X hX hJoint x
    (Eventually.of_forall hheat) v

theorem killingDefectTensor_heat_hasDerivAt
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
    (x : StandardCapSpace) (v : Fin 2 → StandardCapSpace) :
    let H := fun s => killingDefectTensor (G.flow.connection s) (X s)
    HasDerivAt (fun s => H s x v)
      ((G.flow.connection t).tensorLaplacian (H t) x v +
        lichnerowiczReaction (G.flow.connection t) (H t) x v) t :=
  killingDefectTensor_heat_hasDerivAt_positive G ht X hX
    (hJoint.mono (prod_mono Ioo_subset_Ico_self Subset.rfl)) hheat x v

end PoincareConjecture.M35.Uniqueness
