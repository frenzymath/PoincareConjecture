import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.FieldEntropy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem integral_fieldEntropySource {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} {φ : ℝ → ℝ} (hX : ContDiff ℝ ∞ X) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport X) (hφ0 : φ 0 = 0) :
    (∫ x, g.pullbackVolumeDensity id x * fieldEntropySource D X φ x) =
      -(∫ x, g.pullbackVolumeDensity id x * fieldEntropyDissipation D X φ x) := by
  have hS : Integrable (fun x => g.pullbackVolumeDensity id x * fieldEntropySource D X φ x) :=
    ((raw_volumeDensity_contDiff g).continuous.mul
    (fieldEntropySource_contDiff D hX hφ).continuous).integrable_of_hasCompactSupport
      (fieldEntropySource_hasCompactSupport D hc hφ0).mul_left
  have hD : Integrable (fun x => g.pullbackVolumeDensity id x *
      fieldEntropyDissipation D X φ x) := ((raw_volumeDensity_contDiff g).continuous.mul
    (fieldEntropyDissipation_contDiff D hX hφ).continuous).integrable_of_hasCompactSupport
      (fieldEntropyDissipation_hasCompactSupport D hX hφ hc hφ0).mul_left
  have hz := integral_density_laplacian_eq_zero D (hφ.comp (fieldNormSq_contDiff g hX))
    ((fieldNormSq_hasCompactSupport g hc).comp_left hφ0)
  simp only [Function.comp_def] at hz
  have he : (∫ x, g.pullbackVolumeDensity id x *
      D.laplacian (fun y => φ (fieldNormSq g X y)) x) =
      (∫ x, g.pullbackVolumeDensity id x * fieldEntropySource D X φ x) +
        (∫ x, g.pullbackVolumeDensity id x * fieldEntropyDissipation D X φ x) := by
    rw [← integral_add hS hD]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change g.pullbackVolumeDensity id x * D.laplacian (fun y => φ (fieldNormSq g X y)) x = _
      rw [fieldEntropy_balance D hX hφ x, mul_add]
  linarith only [hz, he]

theorem integral_fieldEntropySource_nonpos {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} {φ : ℝ → ℝ}
    (hX : ContDiff ℝ ∞ X) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport X) (hφ0 : φ 0 = 0)
    (hφnn : ∀ s, 0 ≤ φ s) (hφ' : ∀ s, 0 ≤ deriv φ s)
    (hφ'' : ∀ s, 0 ≤ deriv (deriv φ) s) (hR : ∀ x, 0 ≤ D.scalarCurvature x) :
    (∫ x, g.pullbackVolumeDensity id x * fieldEntropySource D X φ x) ≤ 0 := by
  rw [integral_fieldEntropySource D hX hφ hc hφ0]
  apply neg_nonpos.mpr
  apply integral_nonneg
  intro x
  exact mul_nonneg (by rw [raw_volumeDensity_eq]; exact Real.sqrt_nonneg _)
    (fieldEntropyDissipation_nonneg D X φ x (hφnn _) (hφ' _) (hφ'' _) (hR x))

theorem vector_heat_density_entropy_hasDerivWithinAt
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T t : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht : t ∈ Icc 0 T)
    (X : ℝ → StandardCapSpace → StandardCapSpace) (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (x : StandardCapSpace)
    (hheat : HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (fieldTraceHessian (G.flow.connection t) (X t) x)
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Icc 0 T) t) :
    HasDerivWithinAt (fun s => (G.flow.metric s).pullbackVolumeDensity id x *
      φ (fieldNormSq (G.flow.metric s) (X s) x))
      ((G.flow.metric t).pullbackVolumeDensity id x *
        fieldEntropySource (G.flow.connection t) (X t) φ x) (Icc 0 T) t := by
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ hs => ⟨hs.1, hs.2.trans_lt hTlt⟩
  have hq := vector_heat_normSq_hasDerivWithinAt G hT hTlt ht X x hheat
  have he := (hφ (fieldNormSq (G.flow.metric t) (X t) x)).hasDerivAt.comp_hasDerivWithinAt t hq
  have hρ := (raw_volumeDensity_hasDerivWithinAt G.flow (hsub ht) x).mono hsub
  have h := hρ.mul he
  convert! h using 1
  simp only [fieldEntropySource, fieldTraceHessian, fieldNormSq, Function.comp_def]
  ring

end PoincareConjecture.M35.Uniqueness.Heat
