import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.HarmonicTensionPullback











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem hessian_comp_apply {F H : V → V}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (x u v : V) :
    fderiv ℝ (fderiv ℝ (F ∘ H)) x u v =
      fderiv ℝ (fderiv ℝ F) (H x) (fderiv ℝ H x u) (fderiv ℝ H x v) +
        fderiv ℝ F (H x) (fderiv ℝ (fderiv ℝ H) x u v) := by
  have hdF := (contDiff_infty_iff_fderiv.mp hF).2
  have hdH := (contDiff_infty_iff_fderiv.mp hH).2
  have hdFH := (contDiff_infty_iff_fderiv.mp (hF.comp hH)).2
  have heq : (fun y => fderiv ℝ (F ∘ H) y v) =
      fun y => fderiv ℝ F (H y) (fderiv ℝ H y v) := by
    funext y
    rw [fderiv_comp y (hF.differentiable (by simp) (H y)) (hH.differentiable (by simp) y)]
    rfl
  have hleft := (hdFH.differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)
  have hright := ((hdF.differentiable (by simp) (H x)).hasFDerivAt.comp x
      (hH.differentiable (by simp) x).hasFDerivAt).clm_apply
    ((hdH.differentiable (by simp) x).hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  rw [heq] at hleft
  have h := congrArg (fun L : V →L[ℝ] V => L u) (hleft.unique hright)
  simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add, Function.comp_apply, add_comm] using h



theorem mapCovariantHessian_domain_pullback
    (k b : RiemannianMetric n V) (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞)
    (K : LeviCivitaData k) (B : LeviCivitaData b)
    (D : LeviCivitaData (gaugePullbackMetric k Φ))
    {F : V → V} (hF : ContDiff ℝ ∞ F) (x u v : V) :
    mapCovariantHessian D B (F ∘ (Φ : V → V)) x u v =
      mapCovariantHessian K B F (Φ x)
        (fderiv ℝ (Φ : V → V) x u) (fderiv ℝ (Φ : V → V) x v) := by
  have hΦ : ContDiff ℝ ∞ (Φ : V → V) := contMDiff_iff_contDiff.mp Φ.contMDiff
  rw [mapCovariantHessian_apply, mapCovariantHessian_apply, hessian_comp_apply hF hΦ,
    fderiv_comp x (hF.differentiable (by simp) (Φ x)) (hΦ.differentiable (by simp) x)]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  rw [euclideanConnection_pullback k Φ K D, map_add]
  abel



theorem mapTension_domain_pullback
    (k b : RiemannianMetric n V) (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞)
    (K : LeviCivitaData k) (B : LeviCivitaData b)
    (D : LeviCivitaData (gaugePullbackMetric k Φ))
    {F : V → V} (hF : ContDiff ℝ ∞ F) (x : V) :
    mapTension D B (F ∘ (Φ : V → V)) x = mapTension K B F (Φ x) := by
  let e : Module.Basis (Fin n) ℝ V := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let A := Φ.mfderivToContinuousLinearEquiv (by simp) x
  let e' : Module.Basis (Fin n) ℝ V := e.map A.toLinearEquiv
  have he' (i : Fin n) : e' i = fderiv ℝ (Φ : V → V) x (e i) := by
    change A (e i) = _
    have h := congrArg (fun L => L (e i))
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ (by simp) (x := x))
    simp only [mfderiv_eq_fderiv] at h
    convert! h using 1
  have hgram : Matrix.of (fun i j =>
      (gaugePullbackMetric k Φ).inner x (e i) (e j)) =
      Matrix.of (fun i j => k.inner (Φ x) (e' i) (e' j)) := by
    ext i j
    simp only [Matrix.of_apply, gaugePullbackMetric_inner, he']
  rw [mapTension_eq_inverse_gram D B _ x e, mapTension_eq_inverse_gram K B F (Φ x) e', hgram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mapCovariantHessian_domain_pullback k b Φ K B D hF]
  have hslots : mapCovariantHessian K B F (Φ x)
      (fderiv ℝ (Φ : V → V) x (e i)) (fderiv ℝ (Φ : V → V) x (e j)) =
      mapCovariantHessian K B F (Φ x) (e' i) (e' j) := by rw [he', he']
  exact congrArg (fun z : V =>
    (Matrix.of (fun i j => k.inner (Φ x) (e' i) (e' j)))⁻¹ i j • z) hslots

end PoincareConjecture.M35.RadialGauge
