import PoincareConjecture.Proofs.M35.Uniqueness.KillingStationary
import PoincareConjecture.Proofs.M04.ScalarHessian
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.MetricDerivative.ProductRule











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation:max "V" n:max => EuclideanSpace ℝ (Fin n)



theorem euclidean_field_contMDiff {n : ℕ} {X : V n → V n}
    (hX : ContDiff ℝ ∞ X) :
    ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => Bundle.TotalSpace.mk' (V n) y (E := TangentSpace (𝓡 n)) (X y)) := by
  intro x
  rw [Bundle.contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using hX.contMDiff.contMDiffAt⟩



theorem hessian_field_normSq {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (hX : ContDiff ℝ ∞ X)
    (x u v : V n) :
    D.hessian (fun y => g.inner y (X y) (X y)) x u v =
      2 * g.inner x (fieldHessian D X x u v) (X x) +
        2 * g.inner x (D.connection X x v) (D.connection X x u) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hS := euclidean_field_contMDiff hX
  have hC (a : V n) := euclidean_field_contMDiff (contDiff_const (c := a) :
    ContDiff ℝ ∞ (fun _ : V n => a))
  have hN (a : V n) : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => Bundle.TotalSpace.mk' (V n) y (E := TangentSpace (𝓡 n))
        (D.connection X y a)) := by
    rw [← contMDiffOn_univ]
    exact D.contMDiffOn_connection_apply isOpen_univ (fun _ => a) X
      (hC a).contMDiffOn hS.contMDiffOn
  let q : V n → ℝ := fun y => g.inner y (X y) (X y)
  have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q := hS.inner_bundle hS
  have hfirst (y a : V n) : mvfderiv (𝓡 n) q y a =
      2 * g.inner y (D.connection X y a) (X y) := by
    change mvfderiv (𝓡 n) (fun z => g.inner z (X z) (X z)) y a = _
    rw [D.mvfderiv_inner (fun _ => a) X X
      ((hS y).mdifferentiableAt (by simp)) ((hS y).mdifferentiableAt (by simp))]
    rw [g.symm y (X y) (D.connection X y a)]
    ring
  have hfun : (fun y => mvfderiv (𝓡 n) q y v) =
      (fun y => 2 * g.inner y (D.connection X y v) (X y)) := funext (fun y => hfirst y v)
  have hess := M04.hessianOnFields_eq_hessian_of_contMDiff D hq isOpen_univ
    (hC u).contMDiffOn (hC v).contMDiffOn (x := x) (mem_univ x)
  rw [← hess, LeviCivitaData.hessianOnFields, hfun, mvfderiv_const_mul]
  rw [D.mvfderiv_inner (fun _ => u) (fun y => D.connection X y v) X
      ((hN v x).mdifferentiableAt (by simp)) ((hS x).mdifferentiableAt (by simp)), hfirst]
  simp only [fieldHessian, map_sub, sub_apply]
  ring



theorem laplacian_field_normSq {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (hX : ContDiff ℝ ∞ X) (x : V n) :
    D.laplacian (fun y => g.inner y (X y) (X y)) x =
      2 * g.inner x (∑ i, fieldHessian D X x
        (g.orthonormalBasis x i) (g.orthonormalBasis x i)) (X x) +
      2 * ∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
        (D.connection X x (g.orthonormalBasis x i)) := by
  simp only [LeviCivitaData.laplacian, hessian_field_normSq D X hX,
    map_sum, sum_apply, Finset.sum_add_distrib, Finset.mul_sum]



theorem field_normSq_trace_le_laplacian {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (hX : ContDiff ℝ ∞ X) (x : V n) :
    2 * g.inner x (∑ i, fieldHessian D X x
      (g.orthonormalBasis x i) (g.orthonormalBasis x i)) (X x) ≤
      D.laplacian (fun y => g.inner y (X y) (X y)) x := by
  rw [laplacian_field_normSq D X hX]
  apply le_add_of_nonneg_right
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  by_cases hz : D.connection X x (g.orthonormalBasis x i) = 0
  · simp [hz]
  · exact (g.pos x _ hz).le



theorem vector_heat_normSq_hasDerivWithinAt
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T t : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht : t ∈ Icc 0 T)
    (X : ℝ → StandardCapSpace → StandardCapSpace) (x : StandardCapSpace)
    (hheat : HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Icc 0 T) t) :
    HasDerivWithinAt (fun s => (G.flow.metric s).inner x (X s x) (X s x))
      (2 * (G.flow.metric t).inner x (∑ i, fieldHessian (G.flow.connection t) (X t) x
        ((G.flow.metric t).orthonormalBasis x i)
        ((G.flow.metric t).orthonormalBasis x i)) (X t x)) (Icc 0 T) t := by
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ hs => ⟨hs.1, hs.2.trans_lt hTlt⟩
  have huniq := uniqueDiffOn_Icc hT t ht
  have hd := movingMetric_hasDerivWithinAt_pair
    (G.flow.smooth.mono (prod_mono hsub (Subset.refl _))) ht huniq x hheat hheat
  have hmetric := (G.flow.equation t (hsub ht) x (X t x) (X t x)).mono hsub
  rw [hmetric.derivWithin huniq] at hd
  have hpair : (G.flow.metric t).inner x
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (X t x) =
      (G.flow.metric t).inner x (∑ i, fieldHessian (G.flow.connection t) (X t) x
        ((G.flow.metric t).orthonormalBasis x i)
        ((G.flow.metric t).orthonormalBasis x i)) (X t x) +
        (G.flow.connection t).ricci x (X t x) (X t x) := by
    calc
      _ = (G.flow.metric t).inner x (∑ i, fieldHessian (G.flow.connection t) (X t) x
            ((G.flow.metric t).orthonormalBasis x i)
            ((G.flow.metric t).orthonormalBasis x i)) (X t x) +
          (G.flow.metric t).inner x
            (RicciFlow.ricciSharp (G.flow.connection t) x (X t x)) (X t x) := by
        exact congrArg (fun L => L (X t x))
          (((G.flow.metric t).euclideanCoefficients x).map_add _ _)
      _ = _ := by rw [inner_ricciSharp]
  convert! hd using 1
  rw [(G.flow.metric t).symm x (X t x), hpair]
  ring

end PoincareConjecture.M35.Uniqueness
