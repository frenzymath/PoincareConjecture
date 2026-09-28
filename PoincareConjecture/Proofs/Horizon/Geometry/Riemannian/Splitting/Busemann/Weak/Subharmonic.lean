import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Weak.Distribution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Weak.Supports
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]

theorem busemann_distributional_subharmonic_of_distance_comparison
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hcomparison : ∀ (p : M) (A : ℝ), 0 < A →
      ∀ (φ : M → ℝ), ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ →
        HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
        (∀ x ∈ tsupport φ, A ≤ (g.edist p x).toReal) →
        (∫ x, (g.edist p x).toReal * D.laplacian φ x ∂g.volumeMeasure) ≤
          (m : ℝ) / A * ∫ x, φ x ∂g.volumeMeasure)
    (φ : M → ℝ) (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, g.busemann γ x * D.laplacian φ x ∂g.volumeMeasure := by
  have hlapc := D.hasCompactSupport_laplacian hc
  have hlapi : Integrable (D.laplacian φ) g.volumeMeasure :=
    (D.continuous_laplacian hφ).integrable_of_hasCompactSupport hlapc
  have hlap0 : (∫ x, D.laplacian φ x ∂g.volumeMeasure) = 0 := by
    have h := D.integral_mul_laplacian_comm_of_hasCompactSupport_left
      hφ (contMDiff_const (c := (1 : ℝ))) hc
    simpa [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const] using h.symm
  have happ (t : ℝ) :
      (∫ x, g.busemannApprox γ t x * D.laplacian φ x ∂g.volumeMeasure) =
        -(∫ x, (g.edist (γ t) x).toReal * D.laplacian φ x ∂g.volumeMeasure) := by
    simp only [busemannApprox, sub_mul]
    rw [integral_sub (hlapi.const_mul t)
      (D.integrable_mul_laplacian_of_hasCompactSupport_right
        (g.continuous_toReal_edist (γ t)) hφ hc), integral_const_mul, hlap0]
    ring
  have hbound (A : ℝ) (hA : 0 < A) :
      -((m : ℝ) / A * ∫ x, φ x ∂g.volumeMeasure) ≤
        ∫ x, g.busemann γ x * D.laplacian φ x ∂g.volumeMeasure := by
    apply ge_of_tendsto (g.tendsto_integral_busemannApprox_mul_laplacian D hγ hφ hc)
    filter_upwards [g.eventually_le_toReal_edist_line_on_compact γ hγ hc A] with t ht
    rw [happ]
    exact neg_le_neg (hcomparison (γ t) A hA φ hφ hc hφ0 ht)
  have hI : 0 ≤ ∫ x, φ x ∂g.volumeMeasure := integral_nonneg hφ0
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  suffices h : -(∫ x, g.busemann γ x * D.laplacian φ x ∂g.volumeMeasure) ≤ 0 by
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let A := (m : ℝ) * (∫ x, φ x ∂g.volumeMeasure) / ε + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hquot : (m : ℝ) / A * (∫ x, φ x ∂g.volumeMeasure) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hA]
    dsimp [A]
    have hcancel : ((m : ℝ) * (∫ x, φ x ∂g.volumeMeasure) / ε) * ε =
        (m : ℝ) * (∫ x, φ x ∂g.volumeMeasure) := div_mul_cancel₀ _ hε.ne'
    nlinarith
  have hb := hbound A hA
  linarith

end PoincareConjecture.RiemannianMetric
