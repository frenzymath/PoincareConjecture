import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Similarity







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture

section Integral

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T3Space M] [T3Space N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}


theorem RiemannianMetric.setIntegral_scaled_weight_eq_of_metric_similarity
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) {a : ℝ} (ha : 0 < a)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = a * g.inner x v w)
    (K : M → ℝ) (s : Set M) :
    (∫ y in e '' s, a⁻¹ * K (e.symm y) ∂h.volumeMeasure) =
      (Real.sqrt a) ^ n / a * ∫ x in s, K x ∂g.volumeMeasure := by
  let G := rescaledMetric g a ha
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
  simp only [e.symm_apply_apply, G, rescaledMetric_volumeMeasure, Measure.restrict_smul,
    integral_smul_measure, integral_const_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg a), smul_eq_mul]
  rw [div_eq_mul_inv]
  ring



theorem LeviCivitaData.normalized_pos_scalar_integral_le_of_metric_similarity
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (hn : 2 ≤ n)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) {a : ℝ} (ha : 1 ≤ a)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = a * g.inner x v w)
    (K : M → ℝ) (hK : ∀ x, 0 ≤ K x) (s t : Set M) :
    ((∫ x in s, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) /
      (1 + ∫ x in t, K x ∂g.volumeMeasure)) ≤
    ((∫ y in e '' s, max 0 (D'.scalarCurvature y) ∂h.volumeMeasure) /
      (1 + ∫ y in e '' t, a⁻¹ * K (e.symm y) ∂h.volumeMeasure)) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  rw [D.setIntegral_pos_scalarCurvature_eq_of_metric_similarity D' e ha0 hmetric,
    g.setIntegral_scaled_weight_eq_of_metric_similarity h e ha0 hmetric]
  have hfactor : (Real.sqrt a) ^ n / a = (Real.sqrt a) ^ (n - 2) := by
    rw [pow_sub₀ (Real.sqrt a) (Real.sqrt_pos.mpr ha0).ne' hn, Real.sq_sqrt ha0.le,
      div_eq_mul_inv]
  rw [hfactor]
  have hA : 0 ≤ ∫ x in s, max 0 (D.scalarCurvature x) ∂g.volumeMeasure :=
    integral_nonneg (fun x => le_max_left _ _)
  have hB : 0 ≤ ∫ x in t, K x ∂g.volumeMeasure := integral_nonneg hK
  have hF : 1 ≤ (Real.sqrt a) ^ (n - 2) := one_le_pow₀ (Real.one_le_sqrt.mpr ha)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_nonneg hA (sub_nonneg.mpr hF)]

end Integral



theorem tendsto_normalized_pos_scalar_integral_of_metric_similarities
    {n : ℕ} {M N : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, TopologicalSpace (N j)]
    [∀ j, T3Space (M j)] [∀ j, T3Space (N j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, MeasurableSpace (N j)] [∀ j, BorelSpace (N j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (N j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, IsManifold (𝓡 n) ∞ (N j)]
    (g : ∀ j, RiemannianMetric n (M j)) (h : ∀ j, RiemannianMetric n (N j))
    (D : ∀ j, LeviCivitaData (g j)) (D' : ∀ j, LeviCivitaData (h j))
    (e : ∀ j, M j ≃ₘ⟮𝓡 n, 𝓡 n⟯ N j)
    (a : ℕ → ℝ) (ha : ∀ j, 1 ≤ a j) (hn : 2 ≤ n)
    (hmetric : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      (h j).inner (e j x) (mfderiv (𝓡 n) (𝓡 n) (e j) x v)
        (mfderiv (𝓡 n) (𝓡 n) (e j) x w) = a j * (g j).inner x v w)
    (K : ∀ j, M j → ℝ) (hK : ∀ j x, 0 ≤ K j x) (s t : ∀ j, Set (M j))
    (hdiv : Tendsto (fun j =>
      (∫ x in s j, max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) /
      (1 + ∫ x in t j, K j x ∂(g j).volumeMeasure)) atTop atTop) :
    Tendsto (fun j =>
      (∫ y in (e j) '' s j, max 0 ((D' j).scalarCurvature y) ∂(h j).volumeMeasure) /
      (1 + ∫ y in (e j) '' t j, (a j)⁻¹ * K j ((e j).symm y)
        ∂(h j).volumeMeasure)) atTop atTop := by
  apply tendsto_atTop_mono _ hdiv
  intro j
  exact (D j).normalized_pos_scalar_integral_le_of_metric_similarity
    (D' j) hn (e j) (ha j) (hmetric j) (K j) (hK j) (s j) (t j)

end PoincareConjecture
