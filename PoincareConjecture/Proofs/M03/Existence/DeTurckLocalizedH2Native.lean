import PoincareConjecture.Proofs.M03.Existence.DeTurckGeneratorRegularityNative
import PoincareConjecture.Proofs.M03.Existence.NativeLocalizedEllipticEquationNative
import PoincareConjecture.Proofs.M03.Existence.CoordinateEllipticityNative
import Mathlib.Geometry.Manifold.PartitionOfUnity








set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Metric
open scoped Topology SchwartzMap ContDiff LineDeriv Manifold

noncomputable section

universe u

namespace PoincareConjecture.DeTurckLocalizedH2Native

open EuclideanTranslationNative EuclideanDerivativeNative DeTurckDomainRegularityNative
  DeTurckGeneratorRegularityNative NativeLocalizedEllipticEquationNative
  TensorProbeNative TensorHilbertNative ChartMeasureNative NativeChartScalarLocalization

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_compact_coefficient_cutoff {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ cthickening (r + r) K ⊆ U ∧
      ∃ η : 𝓢(E, ℝ), HasCompactSupport η ∧ tsupport η ⊆ U ∧
        ∀ x ∈ cthickening (4 * r) K, η x = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let r : ℝ := δ / 8
  have hr : 0 < r := div_pos hδ (by norm_num)
  have h4δ : 4 * r < δ := by dsimp only [r]; linarith
  obtain ⟨η, hηsmooth, hηrange, hηsupport, hηone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ, E)) (n := (⊤ : ℕ∞))
      (s := thickening δ K) (t := cthickening (4 * r) K)
      isOpen_thickening isClosed_cthickening
      (cthickening_subset_thickening' hδ h4δ K)
  have hηcompact : HasCompactSupport η :=
    HasCompactSupport.of_support_subset_isCompact (hK.cthickening (r := δ))
      (hηsupport.subset.trans (thickening_subset_cthickening δ K))
  have hηU : tsupport η ⊆ U := by
    apply (closure_minimal _ isClosed_cthickening).trans hδU
    exact hηsupport.subset.trans (thickening_subset_cthickening δ K)
  refine ⟨r, hr, (cthickening_mono (by dsimp only [r]; linarith) K).trans hδU,
    hηcompact.toSchwartzMap hηsmooth.contDiff, hηcompact, hηU, ?_⟩
  intro x hx
  exact (hηone x).mp hx

theorem cutoffSchwartz_toLp_eq_multiplier (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    {U : Set E} (hU : IsOpen U) (hφU : tsupport φ ⊆ U)
    (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) (A : 𝓢(E, ℝ))
    (hA : ∀ x ∈ tsupport φ, A x = f x) :
    (cutoffSchwartz φ hφ hU hφU f hf).toLp 2 volume =
      schwartzMultiplier A (φ.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(cutoffSchwartz φ hφ hU hφU f hf).coeFn_toLp 2 volume,
    schwartzMultiplier_coe A (φ.toLp 2 volume), φ.coeFn_toLp 2 volume] with x hc hm hφx
  rw [hc, hm, hφx, cutoffSchwartz_apply]
  by_cases hx : x ∈ tsupport φ
  · rw [hA x hx, mul_comm]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric n M} (d : TensorHilbertNative.Data g)
  (L : FiniteChartLocalizationData d.charts) (a : L.patches)

theorem localizedSchwartz_support (ab : d.ProbeIndex) (h : SmoothTensor (n := n) (M := M)) :
    tsupport (d.localizedSchwartz L a ab h) ⊆ tsupport (L.scalarCutoff a) := by
  have hprod (x : E) : d.localizedSchwartz L a ab h x =
      L.scalarCutoff a x * scalarProbe d.fields h ab ((L.chart a).symm x) := by
    rw [d.localizedSchwartz_apply, L.scalarCutoff_apply]
    by_cases hx : x ∈ (L.chart a).target
    · rw [chartScalar_of_mem _ _ hx, chartScalar_of_mem _ _ hx]
      rfl
    · rw [chartScalar_of_notMem _ _ hx, chartScalar_of_notMem _ _ hx, zero_mul]
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxK
  apply hx
  rw [hprod, image_eq_zero_of_notMem_tsupport hxK, zero_mul]


theorem exists_principal_coefficient_extensions :
    ∃ r : ℝ, 0 < r ∧ cthickening (r + r) (tsupport (L.scalarCutoff a)) ⊆ (L.chart a).target ∧
      ∃ ell : ℝ, 0 < ell ∧ ∃ A : Fin n → Fin n → 𝓢(E, ℝ),
        (∀ i j x, x ∈ thickening (4 * r) (tsupport (L.scalarCutoff a)) →
          A i j x = principalCoefficient g a.val.1.val i j x) ∧
        ∀ x ∈ cthickening (r + r) (tsupport (L.scalarCutoff a)), ∀ ξ : Fin n → ℝ,
          ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j := by
  obtain ⟨r, hr, h2U, η, hη, hηU, hηone⟩ := exists_compact_coefficient_cutoff
    (cutoff_compactSupport d L a) (L.chart a).open_target (cutoff_support_target d L a)
  let A : Fin n → Fin n → 𝓢(E, ℝ) := fun i j =>
    cutoffSchwartz η hη (L.chart a).open_target hηU
      (principalCoefficient g a.val.1.val i j)
      (principalCoefficient_contDiffOn g a.val.1.val i j)
  have hA (i j : Fin n) (x : E)
      (hx : x ∈ cthickening (4 * r) (tsupport (L.scalarCutoff a))) :
      A i j x = principalCoefficient g a.val.1.val i j x := by
    change η x * principalCoefficient g a.val.1.val i j x = _
    rw [hηone x hx, one_mul]
  obtain ⟨c, hc, hcoerc⟩ := DeTurckNative.exists_chartMetric_uniform_ellipticity
    g a.val.1.val ((cutoff_compactSupport d L a).cthickening (r := r + r))
      (by simpa [FiniteChartLocalizationData.chart, FiniteChartData.chart] using h2U)
  refine ⟨r, hr, h2U, c / ((n : ℝ) + 1), by positivity, A, ?_, ?_⟩
  · intro i j x hx
    exact hA i j x (thickening_subset_cthickening _ _ hx)
  · intro x hx ξ
    have hx4 : x ∈ cthickening (4 * r) (tsupport (L.scalarCutoff a)) :=
      cthickening_mono (by linarith) _ hx
    calc
      _ ≤ ∑ i, ∑ j, principalCoefficient g a.val.1.val i j x * ξ i * ξ j := by
        simpa only [DeTurckNative.quadratic, principalCoefficient] using
          quadratic_lower_bound_sum hc (DeTurckNative.chartMetricCoefficients g a.val.1.val x)⁻¹
            (hcoerc x hx) ξ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hA i j x hx4]

theorem principalFluxTest_toLp_eq (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target)
    (A : Fin n → Fin n → 𝓢(E, ℝ))
    (hA : ∀ i j x, x ∈ tsupport φ → A i j x = principalCoefficient g a.val.1.val i j x)
    (i j : Fin n) :
    (principalFluxTest d L a φ hφ hφU i j).toLp 2 volume =
      schwartzMultiplier (A i j) ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume) := by
  unfold principalFluxTest
  simp only [PiLp.basisFun_apply]
  apply cutoffSchwartz_toLp_eq_multiplier
  intro x hx
  exact hA i j x (SchwartzMap.tsupport_lineDerivOp_subset _ _ hx)

theorem principalGradientTest_toLp_eq (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {V : Set E} (hV : IsOpen V) (hφV : tsupport φ ⊆ V)
    (hA : ∀ i j x, x ∈ V → A i j x = principalCoefficient g a.val.1.val i j x)
    (i j : Fin n) :
    (principalGradientTest d L a φ hφ hφU i j).toLp 2 volume =
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A i j)) (φ.toLp 2 volume) := by
  unfold principalGradientTest
  apply cutoffSchwartz_toLp_eq_multiplier
  intro x hx
  have hlocal : (A i j : E → ℝ) =ᶠ[𝓝 x] principalCoefficient g a.val.1.val i j := by
    filter_upwards [hV.mem_nhds (hφV hx)] with y hy
    exact hA i j y hy
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hlocal.fderiv_eq]
  simp only [PiLp.basisFun_apply]

def divergenceSource (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex)
    (b : d.Value) (z : d.Form) : ScalarL2 n :=
  L.localizationL2 a (d.valueCoefficient ab b) + lowerSource d L a ab z -
    ∑ i : Fin n, ∑ j : Fin n,
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A i j)) (d.localizedDerivative L a ab i z)

theorem generatorGraph_extended_divergence_equation
    {r : ℝ} (hr : 0 < r)
    (h2U : cthickening (r + r) (tsupport (L.scalarCutoff a)) ⊆ (L.chart a).target)
    (A : Fin n → Fin n → 𝓢(E, ℝ))
    (hA : ∀ i j x, x ∈ thickening (4 * r) (tsupport (L.scalarCutoff a)) →
      A i j x = principalCoefficient g a.val.1.val i j x)
    {u b : d.Value} (hb : d.GeneratorGraph u b) :
    ∃ z : d.Form, d.inclusion z = u ∧ ‖z‖ ≤ ‖u‖ + ‖b‖ ∧
      ∀ (ab : d.ProbeIndex) (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ),
        tsupport φ ⊆ cthickening (r + r) (tsupport (L.scalarCutoff a)) →
        (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (d.localizedDerivative L a ab i z))
          ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
          inner ℝ (divergenceSource d L a A ab b z) (φ.toLp 2 volume) := by
  obtain ⟨z, hz, hnorm, heq⟩ := generatorGraph_divergence_equation d L a hb
  refine ⟨z, hz, hnorm, ?_⟩
  intro ab φ hφ hφK
  have hφU := hφK.trans h2U
  have hφV : tsupport φ ⊆ thickening (4 * r) (tsupport (L.scalarCutoff a)) :=
    hφK.trans (cthickening_subset_thickening' (by positivity) (by linarith) _)
  have h := heq ab φ hφ hφU
  simp_rw [principalFluxTest_toLp_eq d L a φ hφ hφU A
    (fun i j x hx => hA i j x (hφV hx)),
    principalGradientTest_toLp_eq d L a φ hφ hφU A isOpen_thickening hφV hA,
    ← schwartzMultiplier_selfAdjoint] at h
  simpa only [divergenceSource, inner_sub_left, sum_inner] using h


def divergenceGraphSource (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex) :
    d.Value × d.Form →L[ℝ] ScalarL2 n :=
  ((L.localizationL2 a).comp (d.valueCoefficient ab)).comp
      (ContinuousLinearMap.fst ℝ d.Value d.Form) +
    ((lowerSource d L a ab - ∑ i : Fin n, ∑ j : Fin n,
      (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A i j))).comp
        (d.localizedDerivative L a ab i)).comp
          (ContinuousLinearMap.snd ℝ d.Value d.Form))

theorem divergenceGraphSource_apply (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex)
    (b : d.Value) (z : d.Form) :
    divergenceGraphSource d L a A ab (b, z) = divergenceSource d L a A ab b z := by
  simp only [divergenceGraphSource, divergenceSource, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  abel

set_option synthInstance.maxHeartbeats 200000 in


theorem generatorGraph_localized_H2_schwartz :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u b : d.Value, d.GeneratorGraph u b →
      ∃ z : d.Form, d.inclusion z = u ∧ ‖z‖ ≤ ‖u‖ + ‖b‖ ∧
        ∃ W : d.ProbeIndex → Fin n → Fin n → ScalarL2 n, ∀ ab i j,
          ‖W ab i j‖ ≤ C * (‖u‖ + ‖b‖) ∧
            ∀ φ : 𝓢(E, ℝ),
              inner ℝ (W ab i j) (φ.toLp 2 volume) =
                -(∫ x, d.localizedDerivative L a ab i z x *
                  fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))) := by
  classical
  obtain ⟨s, hs, _, η, _, _, hη⟩ := exists_compact_coefficient_cutoff
    (cutoff_compactSupport d L a) (L.chart a).open_target (cutoff_support_target d L a)
  have hηK : ∀ x ∈ tsupport (L.scalarCutoff a), η x = 1 := by
    intro x hx
    exact hη x (self_subset_cthickening _ hx)
  obtain ⟨r, hr, h2U, ell, hEll, A, hA, hell⟩ := exists_principal_coefficient_extensions d L a
  obtain ⟨B, hB, hAB⟩ := exists_schwartz_matrix_derivative_bound A
  let c : d.ProbeIndex → ℝ := fun ab =>
    (‖divergenceGraphSource d L a A ab‖ +
      (n : ℝ) * B * (∑ i : Fin n, ‖d.localizedDerivative L a ab i‖)) / ell
  have hc (ab : d.ProbeIndex) : 0 ≤ c ab := by dsimp only [c]; positivity
  let C : ℝ := ∑ ab : d.ProbeIndex, c ab
  have hC : 0 ≤ C := Finset.sum_nonneg (fun ab _ => hc ab)
  refine ⟨C, hC, ?_⟩
  intro u b hb
  obtain ⟨z, hz, hnorm, heq⟩ := generatorGraph_extended_divergence_equation d L a
    hr h2U A hA hb
  have hsecond (ab : d.ProbeIndex) :
      ∃ W : Fin n → Fin n → ScalarL2 n, ∀ i j,
        ‖W i j‖ ≤ (‖divergenceSource d L a A ab b z‖ +
          (n : ℝ) * B * (∑ k, ‖d.localizedDerivative L a ab k z‖)) / ell ∧
          ∀ φ : 𝓢(E, ℝ),
            inner ℝ (W i j) (φ.toLp 2 volume) =
              -(∫ x, d.localizedDerivative L a ab i z x *
                fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))) := by
    apply exists_secondDerivatives_of_weak_equation_integrable
      (intoFirstOrderGraph d.fields d.charts.measure)
      (intoFirstOrderGraph_denseRange d.fields d.charts.measure)
      (d.localizedSchwartz L a ab) (d.localizedValue L a ab)
      (fun i => d.localizedDerivative L a ab i)
      (d.localizedValue L a ab).continuous
      (fun i => (d.localizedDerivative L a ab i).continuous)
      (d.localizedValue_into L a ab) (fun i => d.localizedDerivative_into L a ab i)
      A (localizedSchwartz_support d L a ab) hr hEll hB hell hAB
      (divergenceSource d L a A ab b z) z
      (fun i => integrable_localizedDerivative d L a ab i η hηK z)
    intro j h hh f
    apply heq ab (quotientTestSchwartz (d.localizedSchwartz L a ab f)
      (EuclideanSpace.single j (1 : ℝ)) h)
    · exact quotientTestSchwartz_hasCompactSupport _
        ((cutoff_compactSupport d L a).of_isClosed_subset (isClosed_tsupport _)
          (localizedSchwartz_support d L a ab f)) _ _
    · exact tsupport_quotientTestSchwartz_subset _ _ _
        (localizedSchwartz_support d L a ab f) hr.le hh
  choose W hW using hsecond
  refine ⟨z, hz, hnorm, W, ?_⟩
  intro ab i j
  refine ⟨(hW ab i j).1.trans ?_, (hW ab i j).2⟩
  have hpair : ‖(b, z)‖ ≤ ‖u‖ + ‖b‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_left (norm_nonneg _)) hnorm
  have hsource : ‖divergenceSource d L a A ab b z‖ ≤
      ‖divergenceGraphSource d L a A ab‖ * (‖u‖ + ‖b‖) := by
    rw [← divergenceGraphSource_apply]
    exact ((divergenceGraphSource d L a A ab).le_opNorm (b, z)).trans
      (mul_le_mul_of_nonneg_left hpair (norm_nonneg _))
  have hfirst : (∑ k, ‖d.localizedDerivative L a ab k z‖) ≤
      (∑ k, ‖d.localizedDerivative L a ab k‖) * (‖u‖ + ‖b‖) := by
    calc
      _ ≤ ∑ k, ‖d.localizedDerivative L a ab k‖ * ‖z‖ :=
        Finset.sum_le_sum (fun k _ => (d.localizedDerivative L a ab k).le_opNorm z)
      _ = (∑ k, ‖d.localizedDerivative L a ab k‖) * ‖z‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm
        (Finset.sum_nonneg (fun k _ => (d.localizedDerivative L a ab k).opNorm_nonneg))
  calc
    _ ≤ (‖divergenceGraphSource d L a A ab‖ * (‖u‖ + ‖b‖) +
        (n : ℝ) * B * ((∑ k, ‖d.localizedDerivative L a ab k‖) * (‖u‖ + ‖b‖))) / ell :=
      div_le_div_of_nonneg_right (add_le_add hsource
        (mul_le_mul_of_nonneg_left hfirst (mul_nonneg (Nat.cast_nonneg _) hB))) hEll.le
    _ = c ab * (‖u‖ + ‖b‖) := by dsimp only [c]; ring
    _ ≤ C * (‖u‖ + ‖b‖) := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun cd _ => hc cd) (Finset.mem_univ ab)) (by positivity)


theorem generatorGraph_localized_H2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u b : d.Value, d.GeneratorGraph u b →
      ∃ z : d.Form, d.inclusion z = u ∧ ‖z‖ ≤ ‖u‖ + ‖b‖ ∧
        ∃ W : d.ProbeIndex → Fin n → Fin n → ScalarL2 n, ∀ ab i j,
          ‖W ab i j‖ ≤ C * (‖u‖ + ‖b‖) ∧
            ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ →
              inner ℝ (W ab i j) (φ.toLp 2 volume) =
                -(∫ x, d.localizedDerivative L a ab i z x *
                  fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))) := by
  obtain ⟨C, hC, h⟩ := generatorGraph_localized_H2_schwartz d L a
  refine ⟨C, hC, ?_⟩
  intro u b hb
  obtain ⟨z, hz, hnorm, W, hW⟩ := h u b hb
  refine ⟨z, hz, hnorm, W, ?_⟩
  intro ab i j
  exact ⟨(hW ab i j).1, fun φ _ => (hW ab i j).2 φ⟩

end PoincareConjecture.DeTurckLocalizedH2Native

end
