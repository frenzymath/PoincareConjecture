import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ContractedBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Algebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma sum_covariantTensorDerivative_riemannEvaluation_divergence
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (a b c : TangentSpace (𝓡 n) x) :
    ∑ i, D.covariantTensorDerivative D.riemannEvaluation x
        ![g.orthonormalBasis x i, a, g.orthonormalBasis x i, c, b] =
      D.covariantTensorDerivative D.ricciEvaluation x ![b, a, c] -
        D.covariantTensorDerivative D.ricciEvaluation x ![c, a, b] := by
  let e := g.orthonormalBasis x
  have hpoint (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.covariantTensorDerivative D.riemannEvaluation x
          ![e i, a, e i, c, b] =
        D.covariantTensorDerivative D.riemannEvaluation x
          ![b, a, e i, c, e i] -
          D.covariantTensorDerivative D.riemannEvaluation x
            ![c, a, e i, b, e i] := by
    let K := fun (u a b c d : TangentSpace (𝓡 n) x) ↦
      D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d]
    have hcyc := D.covariantTensorDerivative_curvature_second_bianchi hD x
      (e i) a (e i) c b
    have hcyc' := D.covariantTensorDerivative_curvature_second_bianchi hD x
      (e i) c b a (e i)
    have hzero := D.covariantTensorDerivative_riemannEvaluation_skew_first hD x
      a (e i) (e i) c b
    have hfirst := D.covariantTensorDerivative_riemannEvaluation_skew_first hD x
      (e i) c b a (e i)
    have hfirst' := D.covariantTensorDerivative_riemannEvaluation_skew_first hD x
      b a (e i) c (e i)
    have hlast := D.covariantTensorDerivative_riemannEvaluation_skew_last hD x
      c a (e i) (e i) b
    have hpair := D.covariantTensorDerivative_riemannEvaluation_pair_swap hD x
      c (e i) b a (e i)
    have hpair' := D.covariantTensorDerivative_riemannEvaluation_pair_swap hD x
      b (e i) c a (e i)
    have hpairU := D.covariantTensorDerivative_riemannEvaluation_pair_swap hD x
      (e i) (e i) a c b
    have hlastU := D.covariantTensorDerivative_riemannEvaluation_skew_last hD x
      (e i) c b (e i) a
    have hskewX := D.covariantTensorDerivative_riemannEvaluation_skew_first hD x
      c b (e i) a (e i)
    have hlastP := D.covariantTensorDerivative_riemannEvaluation_skew_last hD x
      b a (e i) (e i) c
    linarith
  change (∑ i, D.covariantTensorDerivative D.riemannEvaluation x
      ![e i, a, e i, c, b]) = _
  simp_rw [hpoint]
  have hricci₁ := D.covariantTensorDerivative_ricciEvaluation_eq_sum_riemann hD x b a c
  have hricci₂ := D.covariantTensorDerivative_ricciEvaluation_eq_sum_riemann hD x c a b
  have hricci₁E : D.covariantTensorDerivative D.ricciEvaluation x ![b, a, c] =
      ∑ i, D.covariantTensorDerivative D.riemannEvaluation x ![b, a, e i, c, e i] := by
    simpa [e] using hricci₁
  have hricci₂E : D.covariantTensorDerivative D.ricciEvaluation x ![c, a, b] =
      ∑ i, D.covariantTensorDerivative D.riemannEvaluation x ![c, a, e i, b, e i] := by
    simpa [e] using hricci₂
  rw [Finset.sum_sub_distrib, ← hricci₁E, ← hricci₂E]

lemma sum_curvature_cons_eq_ricci_mul
    (D : LeviCivitaData g) {k : ℕ}
    {A : CovariantTensorEvaluation n M (k + 1)}
    (hA : IsSmoothCovariantTensor A) (x : M)
    (a : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    ∑ i, A x (Fin.cons (D.curvature x a (g.orthonormalBasis x i)
      (g.orthonormalBasis x i)) v) =
    ∑ j, D.ricci x a (g.orthonormalBasis x j) *
        A x (Fin.cons (g.orthonormalBasis x j) v) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := g.orthonormalBasis x
  obtain ⟨B, hB⟩ := hA.1 x
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      A x (Fin.cons (D.curvature x a (e i) (e i)) v) =
        ∑ j, (g.inner x (D.curvature x a (e i) (e i)) (e j)) *
          A x (Fin.cons (e j) v) := by
    let L := B.toLinearMap (Fin.cons (0 : TangentSpace (𝓡 n) x) v) 0
    have hL (q : TangentSpace (𝓡 n) x) : B (Fin.cons q v) = L q := by
      simp only [L, MultilinearMap.toLinearMap_apply]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    have he := congrArg L (e.sum_repr' (D.curvature x a (e i) (e i)))
    simp only [map_sum, map_smul, smul_eq_mul] at he
    change (∑ j, (g.inner x (e j) (D.curvature x a (e i) (e i))) * L (e j)) =
      L (D.curvature x a (e i) (e i)) at he
    have hsymm (u w : TangentSpace (𝓡 n) x) : g.inner x u w = g.inner x w u := by
      change inner ℝ u w = inner ℝ w u
      exact real_inner_comm _ _
    have hcoef : (∑ j, (g.inner x (e j) (D.curvature x a (e i) (e i))) * L (e j)) =
        ∑ j, (g.inner x (D.curvature x a (e i) (e i)) (e j)) * L (e j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsymm]
    rw [hcoef] at he
    simp_rw [hB, hL]
    change L (D.curvature x a (e i) (e i)) =
      ∑ j, (g.inner x (D.curvature x a (e i) (e i)) (e j)) * L (e j)
    simpa only [hL] using he.symm
  change (∑ i, A x (Fin.cons (D.curvature x a (e i) (e i)) v)) = _
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_mul]
  congr 1

end PoincareConjecture.LeviCivitaData
