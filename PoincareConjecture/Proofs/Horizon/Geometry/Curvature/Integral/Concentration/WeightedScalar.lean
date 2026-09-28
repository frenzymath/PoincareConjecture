import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import Mathlib.MeasureTheory.Integral.Bochner.Set









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [MeasurableSpace M] [BorelSpace M] in

theorem scalarCurvature_posPart_le_add_weight
    (D : LeviCivitaData g) (x : M) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ v w : TangentSpace (𝓡 n) x, -K ≤ D.sectionalCurvature x v w) :
    max 0 (D.scalarCurvature x) ≤ D.scalarCurvature x + (n : ℝ) ^ 2 * K := by
  have hb := D.scalarCurvature_lower_bound_of_sectionalCurvature_lower_bound x K hsec
  apply max_le
  · nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hK]
  · exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hK)



theorem integral_scalarCurvature_posPart_le_integral_add_weight
    (D : LeviCivitaData g) {s : Set M} (hs : MeasurableSet s) {K : M → ℝ}
    (hK : ∀ x ∈ s, 0 ≤ K x)
    (hsec : ∀ x ∈ s, ∀ v w : TangentSpace (𝓡 n) x,
      -K x ≤ D.sectionalCurvature x v w)
    (hR : IntegrableOn D.scalarCurvature s g.volumeMeasure)
    (hKi : IntegrableOn K s g.volumeMeasure) :
    (∫ x in s, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      (∫ x in s, D.scalarCurvature x ∂g.volumeMeasure) +
        (n : ℝ) ^ 2 * ∫ x in s, K x ∂g.volumeMeasure := by
  have hP : IntegrableOn (fun x => max 0 (D.scalarCurvature x)) s g.volumeMeasure := by
    simpa only [IntegrableOn, max_comm] using hR.pos_part
  have hb := setIntegral_mono_on hP (hR.add (hKi.const_mul ((n : ℝ) ^ 2))) hs
    (fun x hx => D.scalarCurvature_posPart_le_add_weight x (hK x hx) (hsec x hx))
  simpa only [Pi.add_apply, integral_add hR (hKi.const_mul ((n : ℝ) ^ 2)),
    integral_const_mul] using hb


theorem integral_scalarCurvature_posPart_le_integral_add_weight_of_isCompact
    (D : LeviCivitaData g) {s : Set M} (hs : IsCompact s) {K : M → ℝ}
    (hKc : ContinuousOn K s) (hK : ∀ x ∈ s, 0 ≤ K x)
    (hsec : ∀ x ∈ s, ∀ v w : TangentSpace (𝓡 n) x,
      -K x ≤ D.sectionalCurvature x v w) :
    (∫ x in s, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      (∫ x in s, D.scalarCurvature x ∂g.volumeMeasure) +
        (n : ℝ) ^ 2 * ∫ x in s, K x ∂g.volumeMeasure := by
  exact D.integral_scalarCurvature_posPart_le_integral_add_weight hs.measurableSet
    hK hsec (D.continuous_scalarCurvature.continuousOn.integrableOn_compact hs)
    (hKc.integrableOn_compact hs)



theorem normalized_integral_scalarCurvature_posPart_le_add
    (D : LeviCivitaData g) {s : Set M} (hs : MeasurableSet s) {K : M → ℝ}
    (hK : ∀ x ∈ s, 0 ≤ K x)
    (hsec : ∀ x ∈ s, ∀ v w : TangentSpace (𝓡 n) x,
      -K x ≤ D.sectionalCurvature x v w)
    (hR : IntegrableOn D.scalarCurvature s g.volumeMeasure)
    (hKi : IntegrableOn K s g.volumeMeasure) :
    (∫ x in s, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) /
        (1 + ∫ x in s, K x ∂g.volumeMeasure) ≤
      (∫ x in s, D.scalarCurvature x ∂g.volumeMeasure) /
        (1 + ∫ x in s, K x ∂g.volumeMeasure) + (n : ℝ) ^ 2 := by
  have hI : 0 ≤ ∫ x in s, K x ∂g.volumeMeasure := setIntegral_nonneg hs hK
  have hp : 0 < 1 + ∫ x in s, K x ∂g.volumeMeasure := by linarith
  have hb := D.integral_scalarCurvature_posPart_le_integral_add_weight hs hK hsec hR hKi
  apply (div_le_iff₀ hp).mpr
  rw [add_mul, div_mul_cancel₀ _ hp.ne']
  nlinarith [sq_nonneg (n : ℝ)]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture



theorem tendsto_normalized_scalar_integral_atTop_of_posPart
    {n : ℕ} {M : ℕ → Type*} [∀ j, TopologicalSpace (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (s : ∀ j, Set (M j)) (K : ∀ j, M j → ℝ)
    (hs : ∀ j, MeasurableSet (s j))
    (hK : ∀ j x, x ∈ s j → 0 ≤ K j x)
    (hsec : ∀ j x, x ∈ s j → ∀ v w : TangentSpace (𝓡 n) x,
      -K j x ≤ (D j).sectionalCurvature x v w)
    (hR : ∀ j, IntegrableOn (D j).scalarCurvature (s j) (g j).volumeMeasure)
    (hKi : ∀ j, IntegrableOn (K j) (s j) (g j).volumeMeasure)
    (hlarge : Tendsto
      (fun j => (∫ x in s j, max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) /
        (1 + ∫ x in s j, K j x ∂(g j).volumeMeasure)) atTop atTop) :
    Tendsto
      (fun j => (∫ x in s j, (D j).scalarCurvature x ∂(g j).volumeMeasure) /
        (1 + ∫ x in s j, K j x ∂(g j).volumeMeasure)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [(tendsto_atTop.1 hlarge) (B + (n : ℝ) ^ 2)] with j hj
  have hb := (D j).normalized_integral_scalarCurvature_posPart_le_add
    (hs j) (hK j) (hsec j) (hR j) (hKi j)
  linarith



theorem tendsto_normalized_scalar_integral_atTop_of_posPart_of_isCompact
    {n : ℕ} {M : ℕ → Type*} [∀ j, TopologicalSpace (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (s : ∀ j, Set (M j)) (K : ∀ j, M j → ℝ)
    (hs : ∀ j, IsCompact (s j)) (hKc : ∀ j, ContinuousOn (K j) (s j))
    (hK : ∀ j x, x ∈ s j → 0 ≤ K j x)
    (hsec : ∀ j x, x ∈ s j → ∀ v w : TangentSpace (𝓡 n) x,
      -K j x ≤ (D j).sectionalCurvature x v w)
    (hlarge : Tendsto
      (fun j => (∫ x in s j, max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) /
        (1 + ∫ x in s j, K j x ∂(g j).volumeMeasure)) atTop atTop) :
    Tendsto
      (fun j => (∫ x in s j, (D j).scalarCurvature x ∂(g j).volumeMeasure) /
        (1 + ∫ x in s j, K j x ∂(g j).volumeMeasure)) atTop atTop := by
  exact tendsto_normalized_scalar_integral_atTop_of_posPart g D s K
    (fun j => (hs j).measurableSet) hK hsec
    (fun j => (D j).continuous_scalarCurvature.continuousOn.integrableOn_compact (hs j))
    (fun j => (hKc j).integrableOn_compact (hs j)) hlarge

end PoincareConjecture
