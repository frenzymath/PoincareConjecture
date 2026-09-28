import PoincareConjecture.Proofs.M35.Thm12_28.ScalarDerivativeJets
import PoincareConjecture.Proofs.M35.Thm12_28.CapScalarEstimates
import Mathlib.Analysis.Normed.Operator.NNNorm









set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Filter Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation:max "E" n:max => EuclideanSpace ℝ (Fin n)



theorem scalarGradientNorm_eq_gradient_norm
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E 3) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M) :
    scalarGradientNorm g D x = g.tangentNorm x (D.gradient D.scalarCurvature x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let v := D.gradient D.scalarCurvature x
  have hunit (w : TangentSpace (𝓡 3) x) :
      g.inner x w w = 1 ↔ w ∈ Metric.sphere 0 1 := by
    change inner ℝ w w = 1 ↔ dist w 0 = 1
    rw [real_inner_self_eq_norm_sq, dist_zero_right]
    constructor
    · intro h
      nlinarith [norm_nonneg w]
    · intro h
      rw [h, one_pow]
  have heval (w : TangentSpace (𝓡 3) x) :
      |mvfderiv (𝓡 3) D.scalarCurvature x w| = ‖innerSL ℝ v w‖ := by
    rw [← D.inner_gradient]
    rfl
  have hset : range (fun w : {w : TangentSpace (𝓡 3) x // g.inner x w w = 1} =>
      |mvfderiv (𝓡 3) D.scalarCurvature x w.val|) =
      (fun w => ‖innerSL ℝ v w‖) '' Metric.sphere 0 1 := by
    ext z
    constructor
    · rintro ⟨⟨w, hw⟩, rfl⟩
      exact ⟨w, (hunit w).mp hw, (heval w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, (hunit w).mpr hw⟩, heval w⟩
  change sSup _ = ‖v‖
  rw [hset, (innerSL ℝ v).sSup_sphere_eq_norm, innerSL_apply_norm]



theorem scalar_fderiv_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p : E n)
    (hjet : ∀ m ≤ 3, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => fderiv ℝ (Dseq k).scalarCurvature (pseq k)) atTop
      (𝓝 (fderiv ℝ D.scalarCurvature p)) := by
  let C := continuousMultilinearCurryFin1 ℝ (E n) ℝ
  have heq (f : E n → ℝ) (y : E n) :
      C (iteratedFDeriv ℝ 1 f y) = fderiv ℝ f y := by
    ext v
    simp [C, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  have h := (C.continuous.tendsto _).comp
    (scalarCurvature_jets_tendsto_of_metric_jets Dseq D pseq p 1 hjet)
  simpa only [Function.comp_def, heq] using h



theorem scalarGradientNorm_tendsto_of_metric_jets
    {gseq : ℕ → RiemannianMetric 3 (E 3)} {g : RiemannianMetric 3 (E 3)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E 3) (p : E 3)
    (hjet : ∀ m ≤ 3, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => scalarGradientNorm (gseq k) (Dseq k) (pseq k)) atTop
      (𝓝 (scalarGradientNorm g D p)) := by
  let G := E 3 →L[ℝ] E 3 →L[ℝ] ℝ
  have hzero : Tendsto (fun k => (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (g.euclideanCoefficients p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ (E 3) G).continuous.tendsto _).comp
      (hjet 0 (by omega))
    simpa only [G, iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hi : (g.euclideanCoefficients p).IsInvertible := by convert! g.inner_isInvertible p
  have hinv := (hi.contDiffAt_map_inverse (n := 0)).continuousAt.tendsto.comp hzero
  have hdf := scalar_fderiv_tendsto_of_metric_jets Dseq D pseq p hjet
  have hgrad : Tendsto
      (fun k => (gseq k).euclideanCoefficients (pseq k) |>.inverse
        (fderiv ℝ (Dseq k).scalarCurvature (pseq k))) atTop
      (𝓝 ((g.euclideanCoefficients p).inverse (fderiv ℝ D.scalarCurvature p))) :=
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (hinv.prodMk_nhds hdf)
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
        (hzero.prodMk_nhds hgrad)).prodMk_nhds hgrad))
  have heq (g' : RiemannianMetric 3 (E 3)) (D' : LeviCivitaData g') (x : E 3) :
      D'.gradient D'.scalarCurvature x =
        (g'.euclideanCoefficients x).inverse (fderiv ℝ D'.scalarCurvature x) := by
    simp only [LeviCivitaData.gradient, mvfderiv, mfderiv_eq_fderiv]
    rfl
  simp_rw [scalarGradientNorm_eq_gradient_norm, heq]
  exact hnorm

end PoincareConjecture.M35
