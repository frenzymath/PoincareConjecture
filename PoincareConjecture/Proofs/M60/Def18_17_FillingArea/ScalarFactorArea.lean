import PoincareConjecture.Proofs.M60.Mathlib.ManifoldDerivativeKernel
import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.GramRank
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskRegularity
import PoincareConjecture.Proofs.M60.Mathlib.LocalAlmostEverywhere
import Mathlib.Analysis.Calculus.Rademacher










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle NNReal ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m60AreaDensity_eq_zero_of_scalar_increment_bound (g : RiemannianMetric n M)
    {F : LoopPlane → M} {ell : LoopPlane → ℝ} {z : LoopPlane} {K : ℝ≥0}
    (hell : DifferentiableAt ℝ ell z)
    (hbound : ∀ᶠ y in 𝓝 z,
      g.edist (F y) (F z) ≤ K * ENNReal.ofReal |ell y - ell z|) :
    m60AreaDensity g F z = 0 := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  have hker : LinearMap.ker (fderiv ℝ ell z).toLinearMap ≤
      LinearMap.ker (mfderiv (𝓡 2) (𝓡 n) F z).toLinearMap := by
    intro v hv
    apply M60.mfderiv_apply_eq_zero_of_increment_bound hell (C := K) _ hv
    simpa +instances only [Real.norm_eq_abs] using! hbound
  have hdet : Matrix.det (m60AreaGram g F z) = 0 := by
    by_contra hne
    have hli := (m60AreaGram_det_ne_zero_iff g F z).mp hne
    have hinj := LinearMap.injective_of_linearIndependent
      (f := (mfderiv (𝓡 2) (𝓡 n) F z).toLinearMap)
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.span_eq hli
    have hzero := LinearMap.ker_eq_bot.mpr hinj
    have hnonzero := LinearMap.ker_ne_bot_of_finrank_lt
      (f := (fderiv ℝ ell z).toLinearMap) (by simp [LoopPlane])
    exact hnonzero (le_bot_iff.mp (hker.trans_eq hzero))
  simp only [m60AreaDensity, hdet, max_self, Real.sqrt_zero]




theorem m60AreaIntegral_eq_zero_of_scalar_increment_bound (g : RiemannianMetric n M)
    {F : LoopPlane → M} {ell : LoopPlane → ℝ} {S : Set LoopPlane}
    (hS : IsOpen S) {L K : ℝ≥0} (hell : LipschitzOnWith L ell S)
    (hbound : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (F x) (F y) ≤ K * ENNReal.ofReal |ell x - ell y|) :
    (∀ᵐ z ∂volume.restrict S, m60AreaDensity g F z = 0) ∧
      IntegrableOn (m60AreaDensity g F) S volume ∧
      (∫ z in S, m60AreaDensity g F z) = 0 := by
  have hzero : ∀ᵐ z ∂volume.restrict S, m60AreaDensity g F z = 0 := by
    filter_upwards [hell.ae_differentiableWithinAt (μ := volume) hS.measurableSet,
      ae_restrict_mem hS.measurableSet] with z hz hzS
    apply m60AreaDensity_eq_zero_of_scalar_increment_bound g (K := K)
      (hz.differentiableAt (hS.mem_nhds hzS))
    filter_upwards [hS.mem_nhds hzS] with y hy
    exact hbound y hy z hzS
  have hi : Integrable (fun _ : LoopPlane => (0 : ℝ)) (volume.restrict S) :=
    integrable_zero LoopPlane ℝ (volume.restrict S)
  refine ⟨hzero, hi.congr (Filter.EventuallyEq.symm hzero), ?_⟩
  rw [integral_congr_ae hzero, integral_zero]




theorem m60ScalarFactor_ae_mdifferentiable (g : RiemannianMetric n M)
    {F : LoopPlane → M} {ell : LoopPlane → ℝ} {S : Set LoopPlane}
    (hS : IsOpen S) {L K : ℝ≥0} (hell : LipschitzOnWith L ell S)
    (hbound : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (F x) (F y) ≤ K * ENNReal.ofReal |ell x - ell y|) :
    ∀ᵐ z ∂volume, z ∈ S → MDifferentiableAt (𝓡 2) (𝓡 n) F z := by
  apply m60_ae_mdifferentiable_of_metric_lipschitzOn g hS
    (L := (K : ℝ) * L) (mul_nonneg K.coe_nonneg L.coe_nonneg)
  intro x hx y hy
  have he := hbound x hx y hy
  have hl : |ell x - ell y| ≤ (L : ℝ) * ‖x - y‖ := hell.norm_sub_le hx hy
  have hmul : (K : ℝ≥0∞) * ENNReal.ofReal |ell x - ell y| ≤
      K * ENNReal.ofReal ((L : ℝ) * ‖x - y‖) := by
    gcongr
  refine he.trans (hmul.trans_eq ?_)
  rw [ENNReal.ofReal_mul L.coe_nonneg,
    ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_coe_nnreal, mul_assoc]




theorem m60AreaIntegral_eq_zero_of_locally_scalar_increment_bound
    (g : RiemannianMetric n M) {F : LoopPlane → M} {S : Set LoopPlane}
    (hS : MeasurableSet S)
    (hlocal : ∀ z ∈ S, ∃ (ell : LoopPlane → ℝ) (U : Set LoopPlane) (L K : ℝ≥0),
      IsOpen U ∧ z ∈ U ∧ LipschitzOnWith L ell U ∧
      ∀ x ∈ U, ∀ y ∈ U, g.edist (F x) (F y) ≤ K * ENNReal.ofReal |ell x - ell y|) :
    (∀ᵐ z ∂volume.restrict S, m60AreaDensity g F z = 0) ∧
      IntegrableOn (m60AreaDensity g F) S volume ∧
      (∫ z in S, m60AreaDensity g F z) = 0 := by
  have hzero : ∀ᵐ z ∂volume, z ∈ S → m60AreaDensity g F z = 0 := by
    apply M60.ae_imp_of_locally_ae volume (HereditarilyLindelofSpace.isLindelof S)
    intro z hz
    obtain ⟨ell, U, L, K, hU, hzU, hell, hbound⟩ := hlocal z hz
    have heq := (m60AreaIntegral_eq_zero_of_scalar_increment_bound g hU hell hbound).1
    exact ⟨U, hU.mem_nhds hzU, (ae_restrict_iff' hU.measurableSet).mp heq⟩
  have hz : ∀ᵐ z ∂volume.restrict S, m60AreaDensity g F z = 0 :=
    (ae_restrict_iff' hS).mpr hzero
  have hi : Integrable (fun _ : LoopPlane => (0 : ℝ)) (volume.restrict S) :=
    integrable_zero LoopPlane ℝ (volume.restrict S)
  refine ⟨hz, hi.congr (Filter.EventuallyEq.symm hz), ?_⟩
  rw [integral_congr_ae hz, integral_zero]

end PoincareConjecture
