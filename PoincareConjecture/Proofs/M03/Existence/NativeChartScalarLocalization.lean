import PoincareConjecture.Proofs.M03.Existence.ChartPushforwardLpNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanTranslationNative
import Mathlib.Geometry.Manifold.ContMDiff.Atlas










set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.NativeChartScalarLocalization

open ChartMeasureNative ChartPushforwardLpNative EuclideanTranslationNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def chartScalar (p : M) (f : M → ℝ) : E → ℝ :=
  (chartAt E p).target.indicator (f ∘ (chartAt E p).symm)

theorem chartScalar_of_mem (p : M) (f : M → ℝ) {z : E} (hz : z ∈ (chartAt E p).target) :
    chartScalar p f z = f ((chartAt E p).symm z) := indicator_of_mem hz _

theorem chartScalar_of_notMem (p : M) (f : M → ℝ) {z : E}
    (hz : z ∉ (chartAt E p).target) : chartScalar p f z = 0 := indicator_of_notMem hz _

theorem chartScalar_eventuallyEq (p : M) (f : M → ℝ) {z : E}
    (hz : z ∈ (chartAt E p).target) :
    chartScalar p f =ᶠ[𝓝 z] f ∘ (chartAt E p).symm := by
  filter_upwards [(chartAt E p).open_target.mem_nhds hz] with y hy
  exact chartScalar_of_mem p f hy

theorem support_chartScalar_subset (p : M) {f : M → ℝ} {K : Set M}
    (hfzero : ∀ x ∉ K, f x = 0) : Function.support (chartScalar p f) ⊆ chartAt E p '' K := by
  intro z hz
  by_cases hzt : z ∈ (chartAt E p).target
  · have hnonzero : f ((chartAt E p).symm z) ≠ 0 := by
      rwa [Function.mem_support, chartScalar_of_mem p f hzt] at hz
    have hx : (chartAt E p).symm z ∈ K := by
      by_contra hx
      exact hnonzero (hfzero _ hx)
    exact ⟨(chartAt E p).symm z, hx, (chartAt E p).right_inv hzt⟩
  · exact False.elim (hz (chartScalar_of_notMem p f hzt))

theorem tsupport_chartScalar_subset (p : M) {f : M → ℝ} {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hfzero : ∀ x ∉ K, f x = 0) : tsupport (chartScalar p f) ⊆ chartAt E p '' K :=
  closure_minimal (support_chartScalar_subset p hfzero)
    (hK.image_of_continuousOn ((chartAt E p).continuousOn.mono hKs)).isClosed

theorem chartScalar_compactSupport (p : M) {f : M → ℝ} {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hfzero : ∀ x ∉ K, f x = 0) : HasCompactSupport (chartScalar (n := n) p f) :=
  (hK.image_of_continuousOn ((chartAt E p).continuousOn.mono hKs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_chartScalar_subset p hK hKs hfzero)

theorem contDiff_chartScalar (p : M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hfzero : ∀ x ∉ K, f x = 0) : ContDiff ℝ ∞ (chartScalar (n := n) p f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hzt : z ∈ (chartAt E p).target
  · have hlocal : ContDiffOn ℝ ∞ (f ∘ (chartAt E p).symm) (chartAt E p).target :=
      (hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))).contDiffOn
    exact (hlocal.contDiffAt ((chartAt E p).open_target.mem_nhds hzt)).congr_of_eventuallyEq
      (chartScalar_eventuallyEq p f hzt)
  · have hzsupport : z ∉ tsupport (chartScalar p f) := by
      intro hz
      obtain ⟨x, hxK, rfl⟩ := tsupport_chartScalar_subset p hK hKs hfzero hz
      exact hzt ((chartAt E p).map_source (hKs hxK))
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hzsupport)

theorem fderiv_chartScalar_of_mem (p : M) (f : M → ℝ) {z : E}
    (hz : z ∈ (chartAt E p).target) :
    fderiv ℝ (chartScalar p f) z = fderiv ℝ (f ∘ (chartAt E p).symm) z :=
  (chartScalar_eventuallyEq p f hz).fderiv_eq

theorem fderiv_chartScalar_of_notMem (p : M) {f : M → ℝ} {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hfzero : ∀ x ∉ K, f x = 0) {z : E} (hz : z ∉ chartAt E p '' K) :
    fderiv ℝ (chartScalar p f) z = 0 :=
  fderiv_of_notMem_tsupport ℝ (fun h => hz (tsupport_chartScalar_subset p hK hKs hfzero h))

theorem chartScalar_memLp (p : M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hfzero : ∀ x ∉ K, f x = 0) : MemLp (chartScalar (n := n) p f) 2 volume :=
  (contDiff_chartScalar p hf hK hKs hfzero).continuous.memLp_of_hasCompactSupport
    (chartScalar_compactSupport p hK hKs hfzero)

theorem chartScalar_coordinate_memLp (p : M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hfzero : ∀ x ∉ K, f x = 0) (i : Fin n) :
    MemLp (fun z => fderiv ℝ (chartScalar p f) z (EuclideanSpace.single i 1)) 2 volume :=
  (((contDiff_chartScalar p hf hK hKs hfzero).continuous_fderiv (by simp)).clm_apply
    continuous_const).memLp_of_hasCompactSupport
      ((chartScalar_compactSupport p hK hKs hfzero).fderiv_apply ℝ (EuclideanSpace.single i 1))

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]


theorem chartExtension_chartScalar (p : M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hfzero : ∀ x ∉ K, f x = 0) {μ : Measure M} (hfμ : MemLp f 2 μ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdom : μ.restrict K ≤ C • coordinatePushforward (chartAt E p) K) :
    chartExtensionL2 (chartAt E p) hK.measurableSet hKs hC hdom
      ((chartScalar_memLp p hf hK hKs hfzero).toLp (chartScalar p f)) = hfμ.toLp f := by
  apply Lp.ext
  apply (chartExtensionL2_toLp_coe (chartAt E p) hK.measurableSet hKs hC hdom
    (chartScalar_memLp p hf hK hKs hfzero)).trans
  apply EventuallyEq.trans _ hfμ.coeFn_toLp.symm
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx, chartScalar_of_mem p f ((chartAt E p).map_source (hKs hx)),
      (chartAt E p).left_inv (hKs hx)]
  · rw [indicator_of_notMem hx, hfzero x hx]

end PoincareConjecture.NativeChartScalarLocalization
