import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormContinuity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.ScalarJets

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 12
open scoped Manifold ContDiff Bundle Topology
open Filter

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private lemma koszul_add_left (B : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (u u' v : EuclideanSpace ℝ (Fin n)) :
    metricKoszulCovector B (u + u') v = metricKoszulCovector B u v +
      metricKoszulCovector B u' v := by
  ext w
  simp only [metricKoszulCovector, smul_apply,
    add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
  ring

private lemma koszul_smul_left (B : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (c : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    metricKoszulCovector B (c • u) v = c • metricKoszulCovector B u v := by
  ext w
  simp only [metricKoszulCovector, smul_apply,
    add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul]
  ring

private lemma koszul_add_right (B : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (u v v' : EuclideanSpace ℝ (Fin n)) :
    metricKoszulCovector B u (v + v') = metricKoszulCovector B u v +
      metricKoszulCovector B u v' := by
  ext w
  simp only [metricKoszulCovector, smul_apply,
    add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
  ring

private lemma koszul_smul_right (B : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (c : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    metricKoszulCovector B u (c • v) = c • metricKoszulCovector B u v := by
  ext w
  simp only [metricKoszulCovector, smul_apply,
    add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul]
  ring

theorem euclideanConnection_add_left (D : LeviCivitaData g)
    (u u' v : EuclideanSpace ℝ (Fin n)) :
    D.euclideanConnection (u + u') v =
      D.euclideanConnection u v + D.euclideanConnection u' v := by
  funext x
  simp only [Pi.add_apply, euclideanConnection]
  rw [connection_const_eq_inverse, connection_const_eq_inverse, connection_const_eq_inverse]
  rw [koszul_add_left]
  rw [(g.euclideanCoefficients x).inverse.map_add]

theorem euclideanConnection_smul_left (D : LeviCivitaData g)
    (c : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    D.euclideanConnection (c • u) v = c • D.euclideanConnection u v := by
  funext x
  simp only [Pi.smul_apply, euclideanConnection]
  rw [connection_const_eq_inverse, connection_const_eq_inverse]
  rw [koszul_smul_left]
  rw [(g.euclideanCoefficients x).inverse.map_smul]

theorem euclideanConnection_add_right (D : LeviCivitaData g)
    (u v v' : EuclideanSpace ℝ (Fin n)) :
    D.euclideanConnection u (v + v') =
      D.euclideanConnection u v + D.euclideanConnection u v' := by
  funext x
  simp only [Pi.add_apply, euclideanConnection]
  rw [connection_const_eq_inverse, connection_const_eq_inverse, connection_const_eq_inverse]
  rw [koszul_add_right]
  rw [(g.euclideanCoefficients x).inverse.map_add]

theorem euclideanConnection_smul_right (D : LeviCivitaData g)
    (c : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    D.euclideanConnection u (c • v) = c • D.euclideanConnection u v := by
  funext x
  simp only [Pi.smul_apply, euclideanConnection]
  rw [connection_const_eq_inverse, connection_const_eq_inverse]
  rw [koszul_smul_right]
  rw [(g.euclideanCoefficients x).inverse.map_smul]

private lemma differentiableAt_euclideanConnection (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (D.euclideanConnection u v) x :=
  (D.contDiffAt_euclideanConnection x u v).differentiableAt (by simp)

theorem exists_multilinear_curvatureTensor (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ A : MultilinearMap ℝ (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n)) ℝ,
      ∀ v, D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v := by
  let R : (Fin 4 → EuclideanSpace ℝ (Fin n)) → ℝ := fun v =>
    g.euclideanCoefficients x
      (fderiv ℝ (D.euclideanConnection (v 1) (v 3)) x (v 0) +
        D.euclideanConnection (v 0) (D.euclideanConnection (v 1) (v 3) x) x -
      (fderiv ℝ (D.euclideanConnection (v 0) (v 3)) x (v 1) +
        D.euclideanConnection (v 1) (D.euclideanConnection (v 0) (v 3) x) x)) (v 2)
  have hadd (v : Fin 4 → EuclideanSpace ℝ (Fin n)) (i : Fin 4)
      (a b : EuclideanSpace ℝ (Fin n)) :
      R (Function.update v i (a + b)) = R (Function.update v i a) +
        R (Function.update v i b) := by
    fin_cases i <;>
      simp [R, euclideanConnection_add_left, euclideanConnection_add_right,
        fderiv_add, differentiableAt_euclideanConnection, map_add, map_sub,
        add_apply, sub_apply] <;> ring
  have hsmul (v : Fin 4 → EuclideanSpace ℝ (Fin n)) (i : Fin 4)
      (c : ℝ) (a : EuclideanSpace ℝ (Fin n)) :
      R (Function.update v i (c • a)) = c • R (Function.update v i a) := by
    fin_cases i <;>
      simp [R, euclideanConnection_smul_left, euclideanConnection_smul_right,
        fderiv_const_smul, differentiableAt_euclideanConnection, map_add, map_sub,
        map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul] <;> ring
  refine ⟨MultilinearMap.mk' R hadd hsmul, ?_⟩
  intro v
  change g.inner x (D.curvature x (v 0) (v 1) (v 3)) (v 2) = R v
  rw [curvature_eq_euclideanConnection]
  rfl

theorem tendsto_curvatureTensorNorm_of_metric_jets
    {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (hzero : Tendsto (fun a => (gseq a).euclideanCoefficients x) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun a => fderiv ℝ (gseq a).euclideanCoefficients x) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (htwo : Tendsto
      (fun a => fderiv ℝ (fderiv ℝ (gseq a).euclideanCoefficients) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x))) :
    Tendsto (fun a => (Dseq a).curvatureTensorNorm x) l
      (𝓝 (D.curvatureTensorNorm x)) := by
  have hAseq (a : α) : ∃ A : MultilinearMap ℝ
      (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n)) ℝ,
      ∀ v, (Dseq a).curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v :=
    (Dseq a).exists_multilinear_curvatureTensor x
  have hA : ∃ A : MultilinearMap ℝ
      (fun _ : Fin 4 => EuclideanSpace ℝ (Fin n)) ℝ,
      ∀ v, D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v :=
    D.exists_multilinear_curvatureTensor x
  apply tendsto_curvatureTensorNorm_of_components Dseq D x b hAseq hA
  · intro i j
    have hev : Continuous
        (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => q (b i) (b j)) := by
      fun_prop
    exact hev.continuousAt.tendsto.comp hzero
  · intro i
    exact tendsto_curvatureTensor_of_metric_jets Dseq D x
      (b (i 0)) (b (i 1)) (b (i 2)) (b (i 3)) hzero hone htwo

theorem tendsto_curvatureTensorNorm_of_scalar_metric_jets
    {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun a => (Dseq a).curvatureTensorNorm x) l
      (𝓝 (D.curvatureTensorNorm x)) := by
  obtain ⟨hzero, hone, htwo⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x b h
  exact tendsto_curvatureTensorNorm_of_metric_jets Dseq D x b hzero hone htwo

end PoincareConjecture.LeviCivitaData
