import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

private theorem tendsto_clm_apply
    {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter α}
    {A : α → E →L[ℝ] F} {A₀ : E →L[ℝ] F} {v : α → E} {v₀ : E}
    (hA : Tendsto A l (𝓝 A₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun a => A a (v a)) l (𝓝 (A₀ v₀)) :=
  ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.tendsto _).comp
    (hA.prodMk_nhds hv)

private theorem tendsto_koszul
    {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter α}
    {A : α → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    {A₀ : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {v : α → E} {v₀ : E}
    (hA : Tendsto A l (𝓝 A₀)) (hv : Tendsto v l (𝓝 v₀)) (u : E) :
    Tendsto (fun a => metricKoszulCovector (A a) u (v a)) l
      (𝓝 (metricKoszulCovector A₀ u v₀)) := by
  have hflip : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
  have hflip' : Continuous (fun B : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous
  have h : Continuous (fun p : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) × E =>
      metricKoszulCovector p.1 u p.2) := by
    unfold metricKoszulCovector
    fun_prop
  exact Filter.Tendsto.comp
    (g := fun p : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) × E =>
      metricKoszulCovector p.1 u p.2)
    (f := fun a => (A a, v a)) (h.tendsto (A₀, v₀)) (hA.prodMk_nhds hv)

theorem tendsto_laplacian_of_metric_and_function_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    {fseq : α → EuclideanSpace ℝ (Fin n) → ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (x : EuclideanSpace ℝ (Fin n))
    (hfseq : ∀ a, ContDiffAt ℝ ∞ (fseq a) x) (hf : ContDiffAt ℝ ∞ f x)
    (hmetric : Tendsto (fun a => (gseq a).euclideanCoefficients x) l
      (𝓝 (g.euclideanCoefficients x)))
    (hmetric' : Tendsto (fun a => fderiv ℝ (gseq a).euclideanCoefficients x) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (hfirst : Tendsto (fun a => fderiv ℝ (fseq a) x) l (𝓝 (fderiv ℝ f x)))
    (hsecond : Tendsto (fun a => fderiv ℝ (fderiv ℝ (fseq a)) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ f) x))) :
    Tendsto (fun a => (Dseq a).laplacian (fseq a) x) l (𝓝 (D.laplacian f x)) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hinv : Tendsto (fun a => ((gseq a).inner x).inverse) l
      (𝓝 (g.inner x).inverse) :=
    ((g.inner_isInvertible x).contDiffAt_map_inverse (n := ∞)).continuousAt.tendsto.comp hmetric
  have hdual (i : Fin n) : Tendsto
      (fun a => ((gseq a).inner x).inverse (EuclideanSpace.proj i)) l
      (𝓝 ((g.inner x).inverse (EuclideanSpace.proj i))) :=
    tendsto_clm_apply (E := E →L[ℝ] ℝ) (F := E) hinv tendsto_const_nhds
  have hchristoffel (i : Fin n) :
      Tendsto (fun a => CoordinateExponential.christoffelBilinear
        (gseq a).euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ i)
          (((gseq a).inner x).inverse (EuclideanSpace.proj i))) l
        (𝓝 (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x
          (EuclideanSpace.basisFun (Fin n) ℝ i)
          ((g.inner x).inverse (EuclideanSpace.proj i)))) := by
    simp only [CoordinateExponential.christoffelBilinear_apply, coordinateChristoffel]
    have hK : Tendsto (fun a => metricKoszulCovector
        (fderiv ℝ (gseq a).euclideanCoefficients x)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        (((gseq a).inner x).inverse (EuclideanSpace.proj i))) l
      (𝓝 (metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((g.inner x).inverse (EuclideanSpace.proj i)))) :=
      tendsto_koszul hmetric' (hdual i) _
    exact tendsto_clm_apply (E := E →L[ℝ] ℝ) (F := E) hinv hK
  have hprincipal := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_clm_apply (tendsto_clm_apply hsecond (tendsto_const_nhds
      (x := EuclideanSpace.basisFun (Fin n) ℝ i))) (hdual i)
  have hconnection := tendsto_clm_apply hfirst
    (tendsto_finsetSum Finset.univ fun i _ => hchristoffel i)
  simpa only [laplacian_eq_sum_fderiv_sub_christoffel _ hf,
    laplacian_eq_sum_fderiv_sub_christoffel _ (hfseq _)] using hprincipal.sub hconnection

end PoincareConjecture.LeviCivitaData
