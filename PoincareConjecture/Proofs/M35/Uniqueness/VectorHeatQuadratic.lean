import PoincareConjecture.Proofs.M35.Uniqueness.KillingGradientEnergy
import PoincareConjecture.Proofs.M04.ShiBernsteinEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem killingCovector_normSq {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    (g.tensorNorm (killingCovector g X) x) ^ 2 = g.inner x (X x) (X x) := by
  classical
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let f (a : Fin 1 → Fin d) := (killingCovector g X x (fun i => b (a i))) ^ 2
  change (Real.sqrt (∑ a : Fin 1 → Fin d, f a)) ^ 2 = _
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp f]
  change (∑ j : Fin d, (g.inner x (X x) (b j)) ^ 2) = g.inner x (X x) (X x)
  have hp := b.sum_inner_mul_inner (X x) (X x)
  change (∑ j, g.inner x (X x) (b j) * g.inner x (b j) (X x)) =
    g.inner x (X x) (X x) at hp
  simpa only [g.symm x (b _) (X x), pow_two] using hp

theorem vector_heat_gradient_cross_le {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hX : ContDiff ℝ ∞ X) (x : EuclideanSpace ℝ (Fin n)) :
    let Q := fun y => (g.tensorNorm
      (D.covariantTensorDerivative (killingCovector g X)) y) ^ 2;
    -2 * M04.scalarGradientPairing g (fun y => g.inner y (X y) (X y)) Q x ≤
      Q x ^ 2 + 16 * g.inner x (X x) (X x) *
        (g.tensorNorm (D.covariantTensorDerivative
          (D.covariantTensorDerivative (killingCovector g X))) x) ^ 2 := by
  let A := killingCovector g X
  let K := D.covariantTensorDerivative A
  let q := fun y => g.inner y (X y) (X y)
  let Q := fun y => (g.tensorNorm K y) ^ 2
  let H := (g.tensorNorm (D.covariantTensorDerivative K) x) ^ 2
  let p := M04.scalarGradientPairing g q Q x
  have hA := isSmoothCovariantTensor_killingCovector g X hX
  have hK := M04.isSmoothCovariantTensor_covariantTensorDerivative D hA
  have hqeq : (fun y => (g.tensorNorm A y) ^ 2) = q :=
    funext (fun y => killingCovector_normSq g X y)
  have hq : 0 ≤ q x := by rw [← hqeq]; exact sq_nonneg _
  have hQ : 0 ≤ Q x := sq_nonneg _
  have hH : 0 ≤ H := sq_nonneg _
  have hfirst := M04.scalarGradientSq_tensorNorm_sq_le D hA x
  rw [hqeq] at hfirst
  rw [killingCovector_normSq] at hfirst
  have hsecond := M04.scalarGradientSq_tensorNorm_sq_le D hK x
  have hcs := M04.scalarGradientPairing_sq_le g q Q x
  have hproduct : M04.scalarGradientSq g q x * M04.scalarGradientSq g Q x ≤
      (4 * q x * Q x) * (4 * Q x * H) :=
    mul_le_mul hfirst hsecond (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  have hbound : p ^ 2 ≤ 16 * q x * Q x ^ 2 * H := by
    nlinarith only [hcs.trans hproduct]
  change -2 * p ≤ Q x ^ 2 + 16 * q x * H
  have hrhs : 0 ≤ Q x ^ 2 + 16 * q x * H := by positivity
  nlinarith only [hbound, hrhs, sq_nonneg (Q x ^ 2 - 16 * q x * H),
    sq_nonneg (Q x ^ 2 + 16 * q x * H + 2 * p)]

theorem vector_heat_product_reaction_of_eventually_heat
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T t K B : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht : t ∈ Ioc 0 T)
    (hK : 0 ≤ K) (hB : 0 ≤ B)
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
    (hRm : (G.flow.connection t).curvatureTensorNorm x ≤ K)
    (hbound : (G.flow.metric t).inner x (X t x) (X t x) ≤ B) :
    let Q := fun s y => ((G.flow.metric s).tensorNorm
      ((G.flow.connection s).covariantTensorDerivative
        (killingCovector (G.flow.metric s) (X s))) y) ^ 2
    let q := fun s y => (G.flow.metric s).inner y (X s y) (X s y)
    let F := fun s y => (16 * B + 1 + q s y) * Q s y
    ∃ a : ℝ, HasDerivWithinAt (fun s => F s x) a (Icc 0 T) t ∧
      a - (G.flow.connection t).laplacian (F t) x ≤ 324 * K * F t x - Q t x ^ 2 := by
  let A := 16 * B + 1
  let H := fun s => (G.flow.connection s).covariantTensorDerivative
    (killingCovector (G.flow.metric s) (X s))
  let Q := fun s y => ((G.flow.metric s).tensorNorm (H s) y) ^ 2
  let q := fun s y => (G.flow.metric s).inner y (X s y) (X s y)
  let N := ((G.flow.metric t).tensorNorm ((G.flow.connection t).covariantTensorDerivative
    (H t)) x) ^ 2
  have hH (s : ℝ) : IsSmoothCovariantTensor (H s) :=
    M04.isSmoothCovariantTensor_covariantTensorDerivative _
      (isSmoothCovariantTensor_killingCovector _ _ (hX s))
  have hti : t ∈ Ioo 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  have htj : t ∈ interior (Ico 0 G.lifetime) := by
    simpa only [interior_Ico] using hti
  have hdQ := hasDerivAt_lichnerowicz_normSq G.flow H hH htj x
    (fun v => killingCovectorGradient_lichnerowicz_hasDerivAt_of_eventually_heat
      G hti X hX hJoint x v hheat)
  have hr := lichnerowicz_curvature_pairing_le (G.flow.connection t) (hH t) x hK hRm
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ hs => ⟨hs.1, hs.2.trans_lt hTlt⟩
  have hdq := vector_heat_normSq_dissipation G hT hTlt ⟨ht.1.le, ht.2⟩
    X (hX t) x (hheat.self_of_nhds.mono hsub)
  let a := deriv (fun s => Q s x) t
  have hda : HasDerivAt (fun s => Q s x) a t := hdQ.congr_deriv hdQ.deriv.symm
  have ha : a ≤ (G.flow.connection t).laplacian (Q t) x + 324 * K * Q t x - 2 * N := by
    dsimp only [a]
    rw [hdQ.deriv]
    change _ ≤ _ at hr
    norm_num at hr
    dsimp only [N, Q]
    nlinarith only [hr]
  change HasDerivWithinAt (fun s => q s x)
    ((G.flow.connection t).laplacian (q t) x - 2 * Q t x) (Icc 0 T) t at hdq
  have hd := (hdq.const_add A).mul hda.hasDerivWithinAt
  refine ⟨_, hd, ?_⟩
  have hQs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Q t) :=
    M04.contMDiff_tensorNorm_sq _ (hH t)
  have hqs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (q t) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨(G.flow.metric t).toRiemannianMetric⟩
    exact (euclidean_field_contMDiff (hX t)).inner_bundle
      (euclidean_field_contMDiff (hX t))
  rw [M04.laplacian_const_add_mul _ A hqs hQs]
  have hq : 0 ≤ q t x := by
    change 0 ≤ (G.flow.metric t).inner x (X t x) (X t x)
    by_cases hx : X t x = 0
    · simp [hx]
    · exact ((G.flow.metric t).pos x _ hx).le
  have hcross := vector_heat_gradient_cross_le (G.flow.connection t) (X t) (hX t) x
  change -2 * M04.scalarGradientPairing (G.flow.metric t) (q t) (Q t) x ≤
    Q t x ^ 2 + 16 * q t x * N at hcross
  have hmul := mul_le_mul_of_nonneg_left ha (show 0 ≤ A + q t x by dsimp [A]; positivity)
  have hcoeff : 16 * q t x ≤ 2 * (A + q t x) := by
    change q t x ≤ B at hbound
    dsimp [A]
    linarith
  have hN := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ N from sq_nonneg _)
  change _ ≤ 324 * K * ((A + q t x) * Q t x) - Q t x ^ 2
  nlinarith only [hmul, hcross, hN]

theorem vector_heat_product_reaction
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T t K B : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht : t ∈ Ioc 0 T)
    (hK : 0 ≤ K) (hB : 0 ≤ B)
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
    (x : StandardCapSpace) (hRm : (G.flow.connection t).curvatureTensorNorm x ≤ K)
    (hbound : (G.flow.metric t).inner x (X t x) (X t x) ≤ B) :
    let Q := fun s y => ((G.flow.metric s).tensorNorm
      ((G.flow.connection s).covariantTensorDerivative
        (killingCovector (G.flow.metric s) (X s))) y) ^ 2
    let q := fun s y => (G.flow.metric s).inner y (X s y) (X s y)
    let F := fun s y => (16 * B + 1 + q s y) * Q s y
    ∃ a : ℝ, HasDerivWithinAt (fun s => F s x) a (Icc 0 T) t ∧
      a - (G.flow.connection t).laplacian (F t) x ≤ 324 * K * F t x - Q t x ^ 2 :=
  vector_heat_product_reaction_of_eventually_heat G hT hTlt ht hK hB X hX
    (hJoint.mono (prod_mono Ioo_subset_Ico_self Subset.rfl)) x
    (Eventually.of_forall hheat) hRm hbound

end PoincareConjecture.M35.Uniqueness
