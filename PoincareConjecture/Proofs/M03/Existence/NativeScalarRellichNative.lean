import PoincareConjecture.Proofs.M03.Existence.NativeScalarLocalizationOperators
import PoincareConjecture.Proofs.M03.Existence.NativeChartGradientEnergyNative









set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set
open scoped Topology Manifold ContDiff

universe u v

namespace PoincareConjecture.NativeScalarRellichNative

open TensorProbeNative ChartMeasureNative NativeChartScalarLocalization
  NativeChartGradientEnergyNative EuclideanRellichNative EuclideanMollificationNative
  FiniteLocalizationCompactnessNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  {iota : Type v} [Fintype iota]

variable (g : RiemannianMetric n M) (F : iota → SmoothField (n := n) (M := M))
  (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
    (∑ i, g.inner x (F i x) v • F i x) = v)
  {d : FiniteChartData (n := n) (M := M)} (L : FiniteChartLocalizationData d)

include g hF L


theorem totallyBounded_smooth_scalar {S : Set (Lp ℝ 2 d.measure)} {R : ℝ} (hR : 0 ≤ R)
    (hS : ∀ u ∈ S, ∃ f : M → ℝ,
      ∃ hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f, ∃ hfLp : MemLp f 2 d.measure,
      ∃ hDfLp : ∀ i, MemLp (scalarDirectional (F i) f) 2 d.measure,
      u = hfLp.toLp f ∧
        ‖hfLp.toLp f‖ ^ 2 +
          (∑ i, ‖(hDfLp i).toLp (scalarDirectional (F i) f)‖ ^ 2) ≤ R ^ 2) :
    TotallyBounded S := by
  classical
  apply totallyBounded_of_finite_reconstruction
    (fun a => L.localizationL2 a) L.reconstructionL2
  · intro a
    obtain ⟨C, hC, hgradient⟩ := exists_cutoff_chart_gradientEnergy_bound g F hF
      a.val.1.val (L.weight_smooth a)
      (fun x => by rw [abs_of_nonneg (L.weight_nonneg a x)]; exact L.weight_le_one a x)
      (L.weight_compactSupport a) (L.weight_support_source a)
      (L.weight_zero_off_support a) (L.region_open a).measurableSet
      (L.region_subset_target a) (L.supportImage_subset_region a)
      (L.lowerConstant_pos a) (L.region_measure_lower a)
    apply totallyBounded_supported_C1 (L.supportImage_compact a)
      (R := ‖L.localizationL2 a‖ * R) (D := (C + 1) * R)
      (mul_nonneg (by linarith) hR)
    · rintro u ⟨v, hv, rfl⟩
      obtain ⟨f, hf, hfLp, hDfLp, rfl, henergy⟩ := hS v hv
      have hvR : ‖hfLp.toLp f‖ ≤ R := by
        apply (sq_le_sq₀ (norm_nonneg _) hR).mp
        have hsum : 0 ≤ ∑ i, ‖(hDfLp i).toLp (scalarDirectional (F i) f)‖ ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        linarith
      exact ((L.localizationL2 a).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hvR (norm_nonneg _))
    · rintro u ⟨v, hv, rfl⟩
      obtain ⟨f, hf, hfLp, hDfLp, rfl, henergy⟩ := hS v hv
      have hprod : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => L.weight a x * f x) :=
        (L.weight_smooth a).mul hf
      refine ⟨chartScalar a.val.1.val (fun x => L.weight a x * f x),
        (contDiff_chartScalar a.val.1.val hprod (L.weight_compactSupport a)
          (L.weight_support_source a) (L.localizedProduct_zero a f)).of_le (by simp),
        L.localizedProduct_memLp a hf, ?_, ?_, L.localizationL2_toLp_eq a hf hfLp, ?_⟩
      · exact chartScalar_coordinate_memLp a.val.1.val hprod
          (L.weight_compactSupport a) (L.weight_support_source a) (L.localizedProduct_zero a f)
      · intro z hz
        apply image_eq_zero_of_notMem_tsupport
        exact fun h => hz (tsupport_chartScalar_subset a.val.1.val
          (L.weight_compactSupport a) (L.weight_support_source a)
          (L.localizedProduct_zero a f) h)
      · calc
          _ ≤ C * (‖hfLp.toLp f‖ ^ 2 +
              ∑ i, ‖(hDfLp i).toLp (scalarDirectional (F i) f)‖ ^ 2) :=
            hgradient f hf hfLp hDfLp
          _ ≤ C * R ^ 2 := mul_le_mul_of_nonneg_left henergy hC
          _ ≤ ((C + 1) * R) ^ 2 := by
            nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg R),
              mul_nonneg hC (sq_nonneg R), sq_nonneg R]
  · intro u hu
    obtain ⟨f, hf, hfLp, hDfLp, rfl, henergy⟩ := hS u hu
    exact L.sum_reconstruction_localization f hf hfLp

theorem isCompact_closure_smooth_scalar {S : Set (Lp ℝ 2 d.measure)} {R : ℝ} (hR : 0 ≤ R)
    (hS : ∀ u ∈ S, ∃ f : M → ℝ,
      ∃ hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f, ∃ hfLp : MemLp f 2 d.measure,
      ∃ hDfLp : ∀ i, MemLp (scalarDirectional (F i) f) 2 d.measure,
      u = hfLp.toLp f ∧
        ‖hfLp.toLp f‖ ^ 2 +
          (∑ i, ‖(hDfLp i).toLp (scalarDirectional (F i) f)‖ ^ 2) ≤ R ^ 2) :
    IsCompact (closure S) :=
  (totallyBounded_smooth_scalar g F hF L hR hS).closure.isCompact_of_isClosed isClosed_closure

end PoincareConjecture.NativeScalarRellichNative
