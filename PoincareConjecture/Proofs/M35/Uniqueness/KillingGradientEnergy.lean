import PoincareConjecture.Proofs.M35.Uniqueness.KillingGradientEvolution
import PoincareConjecture.Proofs.M35.Uniqueness.LichnerowiczEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem killingCovectorGradient_lichnerowicz_hasDerivAt_of_eventually_heat
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ioo 0 G.lifetime)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ))
    (x : StandardCapSpace) (v : Fin 2 → StandardCapSpace)
    (hheat : ∀ᶠ y in 𝓝 x, HasDerivWithinAt (fun s => X s y)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) y
          ((G.flow.metric t).orthonormalBasis y i)
          ((G.flow.metric t).orthonormalBasis y i))
        (RicciFlow.ricciSharp (G.flow.connection t) y (X t y))) (Ico 0 G.lifetime) t) :
    let K := fun s => (G.flow.connection s).covariantTensorDerivative
      (killingCovector (G.flow.metric s) (X s))
    HasDerivAt (fun s => K s x v)
      ((G.flow.connection t).tensorLaplacian (K t) x v +
        lichnerowiczReaction (G.flow.connection t) (K t) x v) t := by
  classical
  let D := G.flow.connection t
  let e := (G.flow.metric t).orthonormalBasis x
  let K := fun s => (G.flow.connection s).covariantTensorDerivative
    (killingCovector (G.flow.metric s) (X s))
  have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
  have hd := killingCovectorGradient_heat_hasDerivAt_of_eventually_heat G ht X hX hJoint
    x (v 0) (v 1) hheat
  dsimp only at hd
  rw [hv] at hd
  apply hd.congr_deriv
  have hu0 (q) : Function.update v (0 : Fin 2) (e q) = ![e q, v 1] := by
    ext i
    fin_cases i <;> simp
  have hu1 (q) : Function.update v (1 : Fin 2) (e q) = ![v 0, e q] := by
    ext i
    fin_cases i <;> simp
  have hcurv : (∑ p, ∑ q, D.curvatureTensor x (v 0) (e p) (e q) (v 1) *
      K t x ![e p, e q]) =
      -(∑ p, ∑ q, D.curvatureTensor x (v 0) (e p) (v 1) (e q) *
        K t x ![e p, e q]) := by
    simp_rw [M04.curvatureTensor_swap_last D x (v 0) _ _ (v 1)]
    simp only [neg_mul, Finset.sum_neg_distrib]
  change D.tensorLaplacian (K t) x v -
    (∑ q, D.ricci x (v 0) (e q) * K t x ![e q, v 1]) -
    (∑ q, D.ricci x (v 1) (e q) * K t x ![v 0, e q]) -
    2 * (∑ p, ∑ q, D.curvatureTensor x (v 0) (e p) (e q) (v 1) *
      K t x ![e p, e q]) =
    D.tensorLaplacian (K t) x v + lichnerowiczReaction D (K t) x v
  rw [hcurv]
  change _ = D.tensorLaplacian (K t) x v +
    (2 * (∑ p, ∑ q, D.curvatureTensor x (v 0) (e p) (v 1) (e q) *
      K t x ![e p, e q]) -
      ∑ j : Fin 2, ∑ q, D.ricci x (v j) (e q) * K t x (Function.update v j (e q)))
  rw [Fin.sum_univ_two]
  simp only [hu0, hu1]
  ring

theorem killingCovectorGradient_lichnerowicz_hasDerivAt
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
    let K := fun s => (G.flow.connection s).covariantTensorDerivative
      (killingCovector (G.flow.metric s) (X s))
    HasDerivAt (fun s => K s x v)
      ((G.flow.connection t).tensorLaplacian (K t) x v +
        lichnerowiczReaction (G.flow.connection t) (K t) x v) t :=
  killingCovectorGradient_lichnerowicz_hasDerivAt_of_eventually_heat G ht X hX
    (hJoint.mono (prod_mono Ioo_subset_Ico_self Subset.rfl)) x v
    (Eventually.of_forall hheat)

theorem killingCovectorGradient_normSq {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hX : ContDiff ℝ ∞ X) (x : EuclideanSpace ℝ (Fin n)) :
    (g.tensorNorm (D.covariantTensorDerivative (killingCovector g X)) x) ^ 2 =
      ∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
        (D.connection X x (g.orthonormalBasis x i)) := by
  classical
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let f (a : Fin 2 → Fin d) :=
    (D.covariantTensorDerivative (killingCovector g X) x (fun i => b (a i))) ^ 2
  change (Real.sqrt (∑ a : Fin 2 → Fin d, f a)) ^ 2 = _
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [← (finTwoArrowEquiv (Fin d)).symm.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [f, killingCovector_derivative D X hX]
  change (∑ j : Fin d, (g.inner x (D.connection X x (b i)) (b j)) ^ 2) =
    g.inner x (D.connection X x (b i)) (D.connection X x (b i))
  have hp := b.sum_inner_mul_inner (D.connection X x (b i)) (D.connection X x (b i))
  change (∑ j, g.inner x (D.connection X x (b i)) (b j) *
    g.inner x (b j) (D.connection X x (b i))) =
      g.inner x (D.connection X x (b i)) (D.connection X x (b i)) at hp
  simpa only [g.symm x (b _) (D.connection X x (b i)), pow_two] using hp

theorem vector_heat_normSq_dissipation
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T t : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht : t ∈ Icc 0 T)
    (X : ℝ → StandardCapSpace → StandardCapSpace) (hX : ContDiff ℝ ∞ (X t))
    (x : StandardCapSpace)
    (hheat : HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Icc 0 T) t) :
    HasDerivWithinAt (fun s => (G.flow.metric s).inner x (X s x) (X s x))
      ((G.flow.connection t).laplacian
        (fun y => (G.flow.metric t).inner y (X t y) (X t y)) x -
        2 * ((G.flow.metric t).tensorNorm ((G.flow.connection t).covariantTensorDerivative
          (killingCovector (G.flow.metric t) (X t))) x) ^ 2) (Icc 0 T) t := by
  have hd := vector_heat_normSq_hasDerivWithinAt G hT hTlt ht X x hheat
  apply hd.congr_deriv
  rw [laplacian_field_normSq _ _ hX, killingCovectorGradient_normSq _ _ hX]
  ring

end PoincareConjecture.M35.Uniqueness
