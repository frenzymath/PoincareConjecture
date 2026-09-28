import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Measure
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import Mathlib.MeasureTheory.Integral.Bochner.Set








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff
namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T3Space M] [T3Space N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}


theorem integral_scalarCurvature_eq_of_metric_similarity
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) {a : ℝ} (ha : 0 < a)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = a * g.inner x v w)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : ℝ → E) :
    (∫ y, Ψ (D'.scalarCurvature y) ∂h.volumeMeasure) =
      (Real.sqrt a) ^ n • ∫ x, Ψ (a⁻¹ * D.scalarCurvature x) ∂g.volumeMeasure := by
  rw [← (rescaledMetric_connection g D a ha).integral_scalarCurvature_eq_of_diffeomorph
    D' e (fun x v w => (hmetric x v w).symm) Ψ]
  simp only [rescaledMetric_volumeMeasure, integral_smul_measure,
    rescaledMetric_scalarCurvature, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg a)]


theorem setIntegral_scalarCurvature_eq_of_metric_similarity
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) {a : ℝ} (ha : 0 < a)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = a * g.inner x v w)
    (s : Set M) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : ℝ → E) :
    (∫ y in e '' s, Ψ (D'.scalarCurvature y) ∂h.volumeMeasure) =
      (Real.sqrt a) ^ n • ∫ x in s, Ψ (a⁻¹ * D.scalarCurvature x) ∂g.volumeMeasure := by
  let G := rescaledMetric g a ha
  let DS := rescaledMetric_connection g D a ha
  have hm (x : M) (v w : TangentSpace (𝓡 n) x) :
      G.inner x v w = h.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) :=
    (hmetric x v w).symm
  have hedist := G.edist_eq_of_diffeomorph_metric_pullback h e hm
  have hp := G.measurePreserving_volumeMeasure_of_edist_eq h e.toEquiv hedist
  change MeasurePreserving e G.volumeMeasure h.volumeMeasure at hp
  have hemb : MeasurableEmbedding e :=
    e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  rw [hp.setIntegral_image_emb hemb]
  have hscalar (x : M) : D'.scalarCurvature (e x) = a⁻¹ * D.scalarCurvature x := by
    exact (DS.scalarCurvature_eq_of_local_isometry D' isOpen_univ
      e.contMDiff.contMDiffOn (fun y _ => hm y) (mem_univ x)).symm.trans
        (rescaledMetric_scalarCurvature g D a ha x)
  simp only [hscalar, G, rescaledMetric_volumeMeasure, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg a)]


theorem setIntegral_pos_scalarCurvature_eq_of_metric_similarity
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) {a : ℝ} (ha : 0 < a)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = a * g.inner x v w)
    (s : Set M) :
    (∫ y in e '' s, max 0 (D'.scalarCurvature y) ∂h.volumeMeasure) =
      (Real.sqrt a) ^ n / a *
        ∫ x in s, max 0 (D.scalarCurvature x) ∂g.volumeMeasure := by
  rw [D.setIntegral_scalarCurvature_eq_of_metric_similarity D' e ha hmetric s
    (fun r => max 0 r)]
  have heq (x : M) : max 0 (a⁻¹ * D.scalarCurvature x) =
      a⁻¹ * max 0 (D.scalarCurvature x) := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr ha.le), mul_zero]
  simp only [heq, integral_const_mul, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

end PoincareConjecture.LeviCivitaData
