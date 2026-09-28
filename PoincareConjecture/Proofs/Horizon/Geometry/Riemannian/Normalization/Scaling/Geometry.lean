import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem rescaledMetric_sectionalCurvature
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (x : M) (v w : TangentSpace (𝓡 n) x) :
    (rescaledMetric_connection g D c hc).sectionalCurvature x v w =
      c⁻¹ * D.sectionalCurvature x v w := by
  simp only [LeviCivitaData.sectionalCurvature, rescaledMetric_curvatureTensor,
    rescaledMetric_inner]
  have hden : c * g.inner x v v * (c * g.inner x w w) -
      (c * g.inner x v w) ^ 2 =
      c * (c * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2)) := by ring
  rw [hden, mul_div_mul_left _ _ hc.ne']
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem metricComplete_rescaledMetric [T3Space M]
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (hcomplete : MetricComplete g) : MetricComplete (rescaledMetric g c hc) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₁ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let g' := rescaledMetric g c hc
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g'.inner, g'.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₂ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let C : ℝ≥0 := ⟨Real.sqrt c, Real.sqrt_nonneg c⟩
  have hCeq : (C : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt c) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hCne : C ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have hne : (C : ℝ≥0∞) ≠ 0 := by
    rw [hCeq]
    exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  have hLip : @LipschitzWith M M m₁.toPseudoEMetricSpace m₂.toPseudoEMetricSpace C id := by
    intro x y
    change g'.edist x y ≤ (C : ℝ≥0∞) * g.edist x y
    rw [rescaledMetric_edist, ← hCeq]
  have hAnti : @AntilipschitzWith M M m₁.toPseudoEMetricSpace m₂.toPseudoEMetricSpace C⁻¹ id := by
    intro x y
    change g.edist x y ≤ ((C⁻¹ : ℝ≥0) : ℝ≥0∞) * g'.edist x y
    rw [rescaledMetric_edist, ENNReal.coe_inv hCne, ← hCeq]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, one_mul]
  have hui : @IsUniformInducing M M m₁.toUniformSpace m₂.toUniformSpace id :=
    @AntilipschitzWith.isUniformInducing M M m₁.toPseudoEMetricSpace
      m₂.toPseudoEMetricSpace C⁻¹ id hAnti
      (@LipschitzWith.uniformContinuous M M m₁.toPseudoEMetricSpace
        m₂.toPseudoEMetricSpace C id hLip)
  exact (@IsUniformInducing.completeSpace_congr M M m₁.toUniformSpace
    m₂.toUniformSpace id hui Function.surjective_id).mp hcomplete

theorem rescaledMetric_sectionalCurvature_lower_bound
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (K : ℝ)
    (hsec : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      -K ≤ D.sectionalCurvature x v w) :
    ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      -(K / c) ≤ (rescaledMetric_connection g D c hc).sectionalCurvature x v w := by
  intro x v w
  rw [rescaledMetric_sectionalCurvature]
  have h := mul_le_mul_of_nonneg_left (hsec x v w) (inv_nonneg.mpr hc.le)
  simpa only [mul_neg, div_eq_mul_inv, mul_comm] using h

end PoincareConjecture
