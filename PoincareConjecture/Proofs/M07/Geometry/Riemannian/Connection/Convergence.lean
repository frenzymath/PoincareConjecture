import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean




set_option autoImplicit false
set_option maxSynthPendingDepth 7

open scoped Manifold ContDiff Topology
open Filter

namespace PoincareConjecture

private theorem contDiff_metricKoszulCovector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (u v : V) :
    ContDiff ℝ ∞ (fun B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => metricKoszulCovector B u v) := by
  have hf : ContDiff ℝ ∞ (fun B : V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V (V →L[ℝ] ℝ)).contDiff
  unfold metricKoszulCovector
  fun_prop

namespace LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


noncomputable def euclideanConnection (D : LeviCivitaData g) (u v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => D.connection (fun _ : EuclideanSpace ℝ (Fin n) => v) x u



theorem tendsto_fderiv_connection_const_of_metric_jets
    {ι : Type*} {l : Filter ι}
    {gseq : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n))
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients x) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients x) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (htwo : Tendsto (fun i => fderiv ℝ (fderiv ℝ (gseq i).euclideanCoefficients) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x))) :
    Tendsto (fun i => fderiv ℝ ((Dseq i).euclideanConnection u v) x) l
      (𝓝 (fderiv ℝ (D.euclideanConnection u v) x)) := by
  let V := EuclideanSpace ℝ (Fin n)
  let G := V →L[ℝ] V →L[ℝ] ℝ
  let B := V →L[ℝ] G
  let Φ : G × B → V := fun q => q.1.inverse (metricKoszulCovector q.2 u v)
  have hΦ (g₀ : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
      ContDiffAt ℝ ∞ Φ (g₀.euclideanCoefficients x, fderiv ℝ g₀.euclideanCoefficients x) := by
    have hi : (g₀.euclideanCoefficients x).IsInvertible := by
      convert! g₀.inner_isInvertible x
    let e := ContinuousLinearEquiv.ofBijective (g₀.euclideanCoefficients x)
      (LinearMap.ker_eq_bot.mpr hi.injective) (LinearMap.range_eq_top.mpr hi.surjective)
    have hI0 := (contDiffAt_map_inverse e).comp
        (g₀.euclideanCoefficients x, fderiv ℝ g₀.euclideanCoefficients x)
        (contDiffAt_fst : ContDiffAt ℝ ∞ Prod.fst
          (g₀.euclideanCoefficients x, fderiv ℝ g₀.euclideanCoefficients x))
    have hI : ContDiffAt ℝ ∞ (fun q : G × B => q.1.inverse)
        (g₀.euclideanCoefficients x, fderiv ℝ g₀.euclideanCoefficients x) := by
      change ContDiffAt ℝ ∞ (ContinuousLinearMap.inverse ∘ Prod.fst)
        (g₀.euclideanCoefficients x, fderiv ℝ g₀.euclideanCoefficients x)
      exact hI0
    have hK : ContDiffAt ℝ ∞ (fun q : G × B => metricKoszulCovector q.2 u v)
        (g₀.euclideanCoefficients x, fderiv ℝ g₀.euclideanCoefficients x) :=
      (contDiff_metricKoszulCovector u v).contDiffAt.comp _ contDiffAt_snd
    exact hI.clm_apply hK
  have hchain (g₀ : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (D₀ : LeviCivitaData g₀) :
      fderiv ℝ (D₀.euclideanConnection u v) x =
        (fderiv ℝ Φ (g₀.euclideanCoefficients x, fderiv ℝ g₀.euclideanCoefficients x)).comp
          ((fderiv ℝ g₀.euclideanCoefficients x).prod
            (fderiv ℝ (fderiv ℝ g₀.euclideanCoefficients) x)) := by
    have hG := g₀.contDiffAt_euclideanCoefficients x
    have hB := hG.fderiv_right (m := ∞) (by simp)
    have hc := ((hΦ g₀).differentiableAt (by simp)).hasFDerivAt.comp x
      (((hG.differentiableAt (by simp)).hasFDerivAt).prodMk
        ((hB.differentiableAt (by simp)).hasFDerivAt))
    have heq : D₀.euclideanConnection u v =
        Φ ∘ (fun y => (g₀.euclideanCoefficients y, fderiv ℝ g₀.euclideanCoefficients y)) := by
      funext y
      exact D₀.connection_const_eq_inverse y u v
    rw [heq]
    exact hc.fderiv
  simp_rw [hchain]
  have hdΦ := ((hΦ g).continuousAt_fderiv (by simp)).tendsto.comp
    (hzero.prodMk_nhds hone)
  have hp : Continuous (fun q : B × (V →L[ℝ] B) => q.1.prod q.2) :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous
  have hd := hp.continuousAt.tendsto.comp (hone.prodMk_nhds htwo)
  exact (continuous_fst.clm_comp continuous_snd).continuousAt.tendsto.comp
    (hdΦ.prodMk_nhds hd)

end LeviCivitaData
end PoincareConjecture
