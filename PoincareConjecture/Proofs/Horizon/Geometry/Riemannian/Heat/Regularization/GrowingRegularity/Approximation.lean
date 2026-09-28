import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.Domination
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.Approximation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Spectral

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

open LeviCivitaData

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

theorem tendstoUniformlyOn_integral_of_exhaustion
    (H : ConservativeHeatKernelData g) (D : LeviCivitaData g)
    (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (hkernel : ∀ x y t, H.kernel x y t = dirichletExhaustionKernel
      (fun q => Dirichlet.heatKernelContinuousTime D (S q)) t x y)
    {f : M → ℝ} (hf : Continuous f) {L : ℝ}
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    {u : ℕ → M → ℝ} (hu : ∀ j, Continuous (u j))
    (hb : ∀ j x, |u j x| ≤ |f x|)
    (hl : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (f x)))
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun (j : ℕ) (p : ℝ × M) => ∫ y, u j y * H.kernel p.2 y p.1 ∂g.volumeMeasure)
      (fun p : ℝ × M => ∫ y, f y * H.kernel p.2 y p.1 ∂g.volumeMeasure)
      atTop (Icc a b ×ˢ {x | (g.edist O x).toReal ≤ R}) := by
  obtain ⟨C, hC, hbound⟩ := D.exists_dirichletExhaustionKernel_later_row_bound
    (NeZero.pos n) hc hk hRic (fun q => (S q).isOpen) hΩmono hcover
    (fun q => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S q))
    (fun _ ht x y => D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y)
    O hR ha hab
  have ht : 0 < b + 1 := by linarith
  have he := (H.tendsto_integral_abs_approximation_error hf hLip hu hb hl O ht).const_mul C
  simp only [mul_zero] at he
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with j hj
  intro p hp
  have hp0 : 0 < p.1 := ha.trans_le hp.1.1
  have hfi := H.integrable_weighted_of_distance_lipschitz hf hLip p.2 hp0
  have hui : Integrable (fun y => u j y * H.kernel p.2 y p.1) g.volumeMeasure := by
    apply hfi.mono ((hu j).aestronglyMeasurable.mul
      (H.integrable_kernel p.2 hp0).aestronglyMeasurable)
    filter_upwards [] with y
    simpa only [Pi.mul_apply, norm_mul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (hb j y) (abs_nonneg (H.kernel p.2 y p.1))
  have herr : Integrable (fun y => |u j y - f y| * H.kernel O y (b + 1)) g.volumeMeasure := by
    have hfi' := H.integrable_weighted_of_distance_lipschitz hf hLip O ht
    apply (hfi'.norm.const_mul 2).mono'
      (((hu j).sub hf).abs.aestronglyMeasurable.mul (H.integrable_kernel O ht).aestronglyMeasurable)
    filter_upwards [] with y
    simp only [Pi.mul_apply, Pi.sub_apply, Real.norm_eq_abs, abs_mul,
      abs_abs, abs_of_pos (H.positive O y (b + 1) ht)]
    have habs : |u j y - f y| ≤ 2 * |f y| := (abs_sub _ _).trans (by linarith [hb j y])
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right habs (H.positive O y (b + 1) ht).le
  rw [dist_comm, dist_eq_norm, ← integral_sub hui hfi]
  have hestimate : ‖∫ y, u j y * H.kernel p.2 y p.1 - f y * H.kernel p.2 y p.1
      ∂g.volumeMeasure‖ ≤ C * ∫ y, |u j y - f y| * H.kernel O y (b + 1) ∂g.volumeMeasure := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (herr.const_mul C)
    filter_upwards [] with y
    rw [← sub_mul, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (H.positive p.2 y p.1 hp0)]
    have hk' : H.kernel p.2 y p.1 ≤ C * H.kernel O y (b + 1) := by
      simpa only [hkernel] using hbound p.1 hp.1 p.2 hp.2 y
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hk' (abs_nonneg (u j y - f y))
  exact hestimate.trans_lt hj

theorem tendstoLocallyUniformlyOn_integral_of_exhaustion
    (H : ConservativeHeatKernelData g) (D : LeviCivitaData g)
    (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (hkernel : ∀ x y t, H.kernel x y t = dirichletExhaustionKernel
      (fun q => Dirichlet.heatKernelContinuousTime D (S q)) t x y)
    {f : M → ℝ} (hf : Continuous f) {L : ℝ}
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    {u : ℕ → M → ℝ} (hu : ∀ j, Continuous (u j))
    (hb : ∀ j x, |u j x| ≤ |f x|)
    (hl : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformlyOn
      (fun (j : ℕ) (p : ℝ × M) => ∫ y, u j y * H.kernel p.2 y p.1 ∂g.volumeMeasure)
      (fun p : ℝ × M => ∫ y, f y * H.kernel p.2 y p.1 ∂g.volumeMeasure)
      atTop (Ioi 0 ×ˢ univ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro p hp
  have hp0 : 0 < p.1 := hp.1
  refine ⟨Icc (p.1 / 2) (p.1 + 1) ×ˢ {x | (g.edist p.2 x).toReal ≤ 1}, ?_, ?_⟩
  · apply mem_nhdsWithin_of_mem_nhds
    apply Filter.mem_of_superset
      ((isOpen_Ioo.prod (isOpen_lt (g.continuous_toReal_edist p.2) continuous_const)).mem_nhds
        (show p ∈ Ioo (p.1 / 2) (p.1 + 1) ×ˢ {x | (g.edist p.2 x).toReal < 1} from ?_))
    · intro q hq
      exact ⟨Ioo_subset_Icc_self hq.1,
        (show (g.edist p.2 q.2).toReal < 1 from hq.2).le⟩
    · refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      have heq : g.edist p.2 p.2 = 0 := Manifold.riemannianEDist_self
      simp only [mem_ofPred_eq, heq, ENNReal.toReal_zero]
      norm_num
  · exact H.tendstoUniformlyOn_integral_of_exhaustion D hc hk hRic S hΩmono hcover
      hkernel hf hLip hu hb hl p.2 le_rfl (half_pos hp0) (by linarith)

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
