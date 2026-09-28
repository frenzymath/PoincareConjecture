import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.ScalarJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

private theorem contDiff_koszul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u v : V) : ContDiff ℝ ∞
      (fun B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => metricKoszulCovector B u v) := by
  have hf : ContDiff ℝ ∞ (fun B : V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V (V →L[ℝ] ℝ)).contDiff
  unfold metricKoszulCovector
  fun_prop

variable {n : ℕ} {α : Type*} {l : Filter α}
  {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem tendsto_connection_at_points
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (xseq : α → EuclideanSpace ℝ (Fin n)) (x u : EuclideanSpace ℝ (Fin n))
    {vseq : α → EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin n)}
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (hv : Tendsto vseq l (𝓝 v)) :
    Tendsto (fun i => (Dseq i).euclideanConnection u (vseq i) (xseq i)) l
      (𝓝 (D.euclideanConnection u v x)) := by
  let V := EuclideanSpace ℝ (Fin n)
  have hinv : (g.euclideanCoefficients x).IsInvertible := by convert! g.inner_isInvertible x
  have hi := (hinv.contDiffAt_map_inverse (n := 0)).continuousAt.tendsto.comp hzero
  have hk : Continuous (fun p : (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) × V =>
      metricKoszulCovector p.1 u p.2) := by
    have hf : Continuous (fun B : V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).continuous
    have hf' : Continuous (fun B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ V V (V →L[ℝ] ℝ)).continuous
    unfold metricKoszulCovector
    fun_prop
  have hK := hk.continuousAt.tendsto.comp (hone.prodMk_nhds hv)
  simp_rw [euclideanConnection, connection_const_eq_inverse]
  convert! (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (hi.prodMk_nhds hK) using 1

private theorem tendsto_fderiv_connection_at_points
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (xseq : α → EuclideanSpace ℝ (Fin n)) (x u v : EuclideanSpace ℝ (Fin n))
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (htwo : Tendsto (fun i => fderiv ℝ (fderiv ℝ (gseq i).euclideanCoefficients) (xseq i)) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x))) :
    Tendsto (fun i => fderiv ℝ ((Dseq i).euclideanConnection u v) (xseq i)) l
      (𝓝 (fderiv ℝ (D.euclideanConnection u v) x)) := by
  let V := EuclideanSpace ℝ (Fin n)
  let G := V →L[ℝ] V →L[ℝ] ℝ
  let B := V →L[ℝ] G
  let Φ : G × B → V := fun q => q.1.inverse (metricKoszulCovector q.2 u v)
  have hΦ (g₀ : RiemannianMetric n V) (y : V) :
      ContDiffAt ℝ ∞ Φ (g₀.euclideanCoefficients y, fderiv ℝ g₀.euclideanCoefficients y) := by
    have hi : (g₀.euclideanCoefficients y).IsInvertible := by convert! g₀.inner_isInvertible y
    have hI : ContDiffAt ℝ ∞ (fun q : G × B => q.1.inverse)
        (g₀.euclideanCoefficients y, fderiv ℝ g₀.euclideanCoefficients y) := by
      have hh : ContDiffAt ℝ ∞ (ContinuousLinearMap.inverse : G → _) (g₀.euclideanCoefficients y) :=
        hi.contDiffAt_map_inverse
      exact hh.comp (g₀.euclideanCoefficients y, fderiv ℝ g₀.euclideanCoefficients y)
        contDiffAt_fst
    have hK : ContDiffAt ℝ ∞ (fun q : G × B => metricKoszulCovector q.2 u v)
        (g₀.euclideanCoefficients y, fderiv ℝ g₀.euclideanCoefficients y) :=
      (contDiff_koszul u v).contDiffAt.comp _ contDiffAt_snd
    exact hI.clm_apply hK
  have hchain (g₀ : RiemannianMetric n V) (D₀ : LeviCivitaData g₀) (y : V) :
      fderiv ℝ (D₀.euclideanConnection u v) y =
        (fderiv ℝ Φ (g₀.euclideanCoefficients y, fderiv ℝ g₀.euclideanCoefficients y)).comp
          ((fderiv ℝ g₀.euclideanCoefficients y).prod
            (fderiv ℝ (fderiv ℝ g₀.euclideanCoefficients) y)) := by
    have hG := g₀.contDiffAt_euclideanCoefficients y
    have hB := hG.fderiv_right (m := ∞) (by simp)
    have hc := ((hΦ g₀ y).differentiableAt (by simp)).hasFDerivAt.comp y
      (((hG.differentiableAt (by simp)).hasFDerivAt).prodMk
        ((hB.differentiableAt (by simp)).hasFDerivAt))
    have heq : D₀.euclideanConnection u v =
        Φ ∘ (fun z => (g₀.euclideanCoefficients z, fderiv ℝ g₀.euclideanCoefficients z)) := by
      funext z
      exact D₀.connection_const_eq_inverse z u v
    rw [heq]
    exact hc.fderiv
  simp_rw [hchain]
  have hdΦ := ((hΦ g x).continuousAt_fderiv (by simp)).tendsto.comp (hzero.prodMk_nhds hone)
  have hp : Continuous (fun q : B × (V →L[ℝ] B) => q.1.prod q.2) :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous
  have hd := hp.continuousAt.tendsto.comp (hone.prodMk_nhds htwo)
  exact (continuous_fst.clm_comp continuous_snd).continuousAt.tendsto.comp (hdΦ.prodMk_nhds hd)

theorem tendsto_curvatureTensor_of_metric_jets_at_points
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (xseq : α → EuclideanSpace ℝ (Fin n)) (x u v w z : EuclideanSpace ℝ (Fin n))
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (htwo : Tendsto (fun i => fderiv ℝ (fderiv ℝ (gseq i).euclideanCoefficients) (xseq i)) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x))) :
    Tendsto (fun i => (Dseq i).curvatureTensor (xseq i) u v w z) l
      (𝓝 (D.curvatureTensor x u v w z)) := by
  have hc a b := tendsto_connection_at_points Dseq D xseq x a hzero hone
    (tendsto_const_nhds (x := b))
  have hd a b (c : EuclideanSpace ℝ (Fin n)) :=
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      ((tendsto_fderiv_connection_at_points Dseq D xseq x a b hzero hone htwo).prodMk_nhds
        (tendsto_const_nhds (x := c)))
  have hn a b c := tendsto_connection_at_points Dseq D xseq x a hzero hone (hc b c)
  have hcurv : Tendsto (fun i => (Dseq i).curvature (xseq i) u v z) l
      (𝓝 (D.curvature x u v z)) := by
    simp_rw [curvature_eq_euclideanConnection]
    convert! ((hd v z u).add (hn u v z)).sub ((hd u z v).add (hn v u z)) using 1
  have hp := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (hzero.prodMk_nhds hcurv)
  convert! (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (hp.prodMk_nhds (tendsto_const_nhds (x := w))) using 1

theorem tendsto_scalarCurvature_of_metric_jets_at_points
    {gseq : α → RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))}
    {g : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (xseq : α → EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2))
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (htwo : Tendsto (fun i => fderiv ℝ (fderiv ℝ (gseq i).euclideanCoefficients) (xseq i)) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x))) :
    Tendsto (fun i => (Dseq i).scalarCurvature (xseq i)) l (𝓝 (D.scalarCurvature x)) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hdet (g₀ : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))) (y : EuclideanSpace ℝ (Fin 2)) :
      g₀.inner y (b 0) (b 0) * g₀.inner y (b 1) (b 1) -
        g₀.inner y (b 0) (b 1) * g₀.inner y (b 1) (b 0) ≠ 0 := by
    have h := g₀.pullback_gram_det_ne_zero y (LinearMap.id) Function.injective_id
    change (Matrix.of (fun a c : Fin 2 => g₀.inner y (b a) (b c))).det ≠ 0 at h
    simpa only [Matrix.det_fin_two, Matrix.of_apply] using h
  have heq (g₀ : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))) (D₀ : LeviCivitaData g₀)
      (y : EuclideanSpace ℝ (Fin 2)) :
      D₀.scalarCurvature y = 2 * D₀.curvatureTensor y (b 0) (b 1) (b 0) (b 1) /
        (g₀.inner y (b 0) (b 0) * g₀.inner y (b 1) (b 1) -
          g₀.inner y (b 0) (b 1) * g₀.inner y (b 1) (b 0)) := by
    rw [D₀.curvatureTensor_eq_half_scalarCurvature]
    field_simp [hdet g₀ y]
  have hcoeff (a c : Fin 2) :=
    ((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
        (hzero.prodMk_nhds (tendsto_const_nhds (x := b a)))).prodMk_nhds
          (tendsto_const_nhds (x := b c))))
  have hcurv := tendsto_curvatureTensor_of_metric_jets_at_points Dseq D xseq x
    (b 0) (b 1) (b 0) (b 1) hzero hone htwo
  simp_rw [heq]
  exact (tendsto_const_nhds.mul hcurv).div
    (((hcoeff 0 0).mul (hcoeff 1 1)).sub ((hcoeff 0 1).mul (hcoeff 1 0))) (hdet g x)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

theorem tendsto_euclideanCoefficients_of_scalar_jets_at_points
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (xseq : α → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) (xseq i)) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x)) ∧
    Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)) ∧
    Tendsto (fun i => fderiv ℝ (fderiv ℝ (gseq i).euclideanCoefficients) (xseq i)) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x)) := by
  have hev (r : ℕ) (hr : r ≤ 2) (a c : ι)
      (v : Fin r → EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun i => (iteratedFDeriv ℝ r (gseq i).euclideanCoefficients (xseq i) v)
        (b a) (b c)) l
        (𝓝 ((iteratedFDeriv ℝ r g.euclideanCoefficients x v) (b a) (b c))) := by
    have hh := (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin r => EuclideanSpace ℝ (Fin n)) ℝ v).continuous.continuousAt.tendsto.comp
        (h r hr a c)
    simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply,
      iteratedFDeriv_inner_eq] using hh
  refine ⟨?_, ?_, ?_⟩
  · apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro a
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro c
    simpa using hev 0 (by omega) a c (fun i => Fin.elim0 i)
  · apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro u
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro a
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro c
    simpa using hev 1 (by omega) a c (fun _ => b u)
  · apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro u
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro v
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro a
    apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
    intro c
    simpa [iteratedFDeriv_two_apply] using
      hev 2 (by omega) a c (fun j => if j = 0 then b u else b v)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

theorem tendsto_scalarCurvature_of_scalar_metric_jets_at_points
    {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))}
    {g : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (xseq : α → EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin 2)))
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) (xseq i)) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (Dseq i).scalarCurvature (xseq i)) l (𝓝 (D.scalarCurvature x)) := by
  obtain ⟨hzero, hone, htwo⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets_at_points xseq x b h
  exact tendsto_scalarCurvature_of_metric_jets_at_points Dseq D xseq x hzero hone htwo

end PoincareConjecture.LeviCivitaData
