import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Averaging
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.InitialContinuity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Gaussian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.KarpLi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Bochner.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz











set_option autoImplicit false

open MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

namespace ConservativeHeatKernelData

variable {g : RiemannianMetric n M}


lemma integrable_kernel (H : ConservativeHeatKernelData g) (x : M) {t : ℝ}
    (ht : 0 < t) :
    Integrable (fun y ↦ H.kernel x y t) (volumeMeasure g) := by
  exact integrable_of_integral_eq_one (H.mass_one x t ht)


lemma integrable_weighted_of_distance_lipschitz
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L : ℝ} (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    (x : M) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y ↦ f y * H.kernel x y t) (volumeMeasure g) := by
  have hk := H.integrable_kernel x ht
  have hd := H.first_moment_integrable x t ht
  apply ((hk.const_mul |f x|).add (hd.const_mul L)).mono'
    (hf.aestronglyMeasurable.mul hk.aestronglyMeasurable)
  filter_upwards [] with y
  change |f y * H.kernel x y t| ≤
    |f x| * H.kernel x y t + L * ((g.edist x y).toReal * H.kernel x y t)
  rw [abs_mul, abs_of_pos (H.positive x y t ht)]
  calc
    |f y| * H.kernel x y t ≤
        (|f x| + L * (g.edist x y).toReal) * H.kernel x y t := by
      have hfy : |f y| ≤ |f x| + |f y - f x| := by
        calc
          |f y| = |f x + (f y - f x)| := by congr 1 <;> ring
          _ ≤ |f x| + |f y - f x| := abs_add_le _ _
      have hsum : |f y| ≤ |f x| + L * (g.edist x y).toReal := by
        linarith [hLip x y]
      exact mul_le_mul_of_nonneg_right hsum (le_of_lt (H.positive x y t ht))
    _ = |f x| * H.kernel x y t +
        L * ((g.edist x y).toReal * H.kernel x y t) := by ring


lemma abs_kernel_integral_sub_le_integral_distance
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L : ℝ} (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    (x : M) {t : ℝ} (ht : 0 < t) :
    |(∫ y, f y * H.kernel x y t ∂volumeMeasure g) - f x| ≤
      L * ∫ y, (g.edist x y).toReal * H.kernel x y t ∂volumeMeasure g := by
  have hk := H.integrable_kernel x ht
  have hfw := H.integrable_weighted_of_distance_lipschitz hf hLip x ht
  have hdiff : Integrable (fun y ↦ (f y - f x) * H.kernel x y t)
      (volumeMeasure g) := by
    rw [show (fun y ↦ (f y - f x) * H.kernel x y t) =
        (fun y ↦ f y * H.kernel x y t) - (fun y ↦ f x * H.kernel x y t) by
      funext y; simp only [Pi.sub_apply]; ring]
    exact hfw.sub (hk.const_mul (f x))
  have hbound : ∀ᵐ y ∂volumeMeasure g,
      ‖(f y - f x) * H.kernel x y t‖ ≤
        L * ((g.edist x y).toReal * H.kernel x y t) := by
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (H.positive x y t ht)]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hLip x y)
        (le_of_lt (H.positive x y t ht))
  have havg := norm_integral_le_of_norm_le
    (H.first_moment_integrable x t ht |>.const_mul L) hbound
  have hsub :
      (∫ y, (f y - f x) * H.kernel x y t ∂volumeMeasure g) =
        (∫ y, f y * H.kernel x y t ∂volumeMeasure g) - f x := by
    calc
      (∫ y, (f y - f x) * H.kernel x y t ∂volumeMeasure g) =
          ∫ y, (f y * H.kernel x y t - f x * H.kernel x y t) ∂volumeMeasure g := by
            congr 1
            funext y
            ring
      _ = (∫ y, f y * H.kernel x y t ∂volumeMeasure g) - f x := by
        rw [integral_sub hfw (hk.const_mul (f x)), integral_const_mul,
          H.mass_one x t ht, mul_one]
  rw [hsub, integral_const_mul] at havg
  simpa [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using havg



theorem regularization_displacement_bound
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L C : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    (hC : ∀ x t, 0 < t → t ≤ 1 →
      ∫ y, (g.edist x y).toReal * H.kernel x y t ∂volumeMeasure g ≤ C)
    {x : M} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |(∫ y, f y * H.kernel x y t ∂volumeMeasure g) - f x| ≤ L * C := by
  exact (H.abs_kernel_integral_sub_le_integral_distance hf hLip x ht).trans
    (mul_le_mul_of_nonneg_left (hC x t ht ht1) hL)




theorem tendstoUniformly_kernel_integral
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal) :
    TendstoUniformly (fun t x ↦ ∫ y, f y * H.kernel x y t ∂volumeMeasure g)
      f (𝓝[>] 0) := by
  obtain ⟨C, _, hC⟩ := H.first_moment_bound
  have hlim : Tendsto (fun t ↦ L *
      ⨆ x, ∫ y, (g.edist x y).toReal * H.kernel x y t ∂volumeMeasure g)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using H.first_moment_tendsto_zero.const_mul L
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 from
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds),
    hlim.eventually (gt_mem_nhds hε)] with t ht ht1 hεt
  intro x
  have hb : BddAbove (Set.range (fun z ↦
      ∫ y, (g.edist z y).toReal * H.kernel z y t ∂volumeMeasure g)) :=
    ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z t ht ht1.le⟩
  rw [Real.dist_eq, abs_sub_comm]
  exact ((H.abs_kernel_integral_sub_le_integral_distance hf hLip x ht).trans
    (mul_le_mul_of_nonneg_left (le_ciSup hb x) hL)).trans_lt hεt



theorem kernel_integral_linear_growth
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L C : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    (O : M) (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hC : ∀ x t, 0 < t → t ≤ 1 →
      ∫ y, (g.edist x y).toReal * H.kernel x y t ∂volumeMeasure g ≤ C)
    {x : M} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |∫ y, f y * H.kernel x y t ∂volumeMeasure g| ≤
      (g.edist O x).toReal + (1 + L * C) := by
  have hdisp := H.regularization_displacement_bound hf hL hLip hC ht ht1 (x := x)
  have hfbound : |f x| ≤ (g.edist O x).toReal + 1 := by
    have h := abs_add_le (f x - (g.edist O x).toReal) (g.edist O x).toReal
    rw [sub_add_cancel, abs_of_nonneg ENNReal.toReal_nonneg] at h
    linarith [happrox x]
  have h := abs_add_le
    ((∫ y, f y * H.kernel x y t ∂volumeMeasure g) - f x) (f x)
  rw [sub_add_cancel] at h
  linarith



theorem continuousOn_kernel_evolution
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    {F : ℝ × M → ℝ}
    (hF : ContinuousOn F (Set.Ioi 0 ×ˢ Set.univ))
    (hrep : ∀ t, 0 < t → ∀ x,
      F (t, x) = ∫ y, f y * H.kernel x y t ∂volumeMeasure g)
    (hzero : ∀ x, F (0, x) = f x) :
    ContinuousOn F (Set.Ici 0 ×ˢ Set.univ) := by
  apply Poincare.Parabolic.continuousOn_nonneg_of_tendstoUniformly hF hf _ hzero
  intro u hu
  filter_upwards [H.tendstoUniformly_kernel_integral hf hL hLip u hu,
    self_mem_nhdsWithin] with t ht ht0
  intro x
  simpa only [hrep t ht0 x] using ht x




theorem integrable_gaussian_kernel_evolution_energy [PreconnectedSpace M]
    (H : ConservativeHeatKernelData g) (hcomplete : MetricComplete g)
    {f : M → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    (O : M) (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F
      (Set.Ioi 0 ×ˢ Set.univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (H.connection.laplacian (fun y ↦ F (t, y)) x) t)
    (hrep : ∀ t, 0 < t → ∀ x,
      F (t, x) = ∫ y, f y * H.kernel x y t ∂volumeMeasure g)
    (hzero : ∀ x, F (0, x) = f x)
    {V c a : ℝ} (hV : 0 ≤ V) (ha : 0 < a)
    (hvol : ∀ R : ℝ, 1 ≤ R →
      (g.volumeMeasure {x | (g.edist O x).toReal ≤ R}).toReal ≤ V * Real.exp (c * R)) :
    Integrable (fun p : ℝ × M ↦ Real.exp (-a * (g.edist O p.2).toReal ^ 2) *
      g.inner p.2 (H.connection.gradient (fun y ↦ F (p.1, y)) p.2)
        (H.connection.gradient (fun y ↦ F (p.1, y)) p.2))
      ((volume.restrict (Set.Ioc 0 1)).prod g.volumeMeasure) := by
  obtain ⟨C, hCpos, hC⟩ := H.first_moment_bound
  apply H.connection.integrable_gaussian_heat_energy hcomplete O hF
    (H.continuousOn_kernel_evolution hf hL hLip hF.continuousOn hrep hzero) hheat
    (A := 1 + L * C) (by positivity) zero_lt_one hV ha _ hvol
  intro t ht x
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · rw [← ht0, hzero]
    have h := abs_add_le (f x - (g.edist O x).toReal) (g.edist O x).toReal
    rw [sub_add_cancel, abs_of_nonneg ENNReal.toReal_nonneg] at h
    have hLC : 0 ≤ L * C := mul_nonneg hL hCpos.le
    linarith [happrox x]
  · rw [hrep t ht0]
    exact H.kernel_integral_linear_growth hf hL hLip O happrox hC ht0 ht.2

end ConservativeHeatKernelData


theorem integrable_of_distance_lipschitz (g : RiemannianMetric n M)
    {f : M → ℝ} (hf : Continuous f) {L : ℝ}
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    (x : M) (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : Integrable (fun y ↦ (g.edist x y).toReal) μ) : Integrable f μ := by
  apply ((integrable_const |f x|).add (hμ.const_mul L)).mono'
    hf.aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs]
  calc
    |f y| = |f x + (f y - f x)| := by congr 1; ring
    _ ≤ |f x| + |f y - f x| := abs_add_le _ _
    _ ≤ |f x| + L * (g.edist x y).toReal := by linarith [hLip x y]



theorem abs_integral_sub_le_integral_distance (g : RiemannianMetric n M)
    {f : M → ℝ} (hf : Continuous f) {L : ℝ}
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    (x : M) (μ : Measure M) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y ↦ (g.edist x y).toReal) μ) :
    |(∫ y, f y ∂μ) - f x| ≤ L * ∫ y, (g.edist x y).toReal ∂μ := by
  have hint := g.integrable_of_distance_lipschitz hf hLip x μ hμ
  have hbound : ∀ᵐ y ∂μ, ‖f y - f x‖ ≤ L * (g.edist x y).toReal := by
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs] using hLip x y
  have havg := norm_integral_le_of_norm_le (hμ.const_mul L) hbound
  rw [integral_sub hint (integrable_const _), integral_const_mul] at havg
  simpa [Real.norm_eq_abs] using havg



theorem tendstoUniformly_integral_of_distance_moment (g : RiemannianMetric n M)
    {f : M → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    {ι : Type*} {l : Filter ι} (μ : ι → M → Measure M)
    [∀ i x, IsProbabilityMeasure (μ i x)]
    (hμ : ∀ i x, Integrable (fun y ↦ (g.edist x y).toReal) (μ i x))
    {a : ι → ℝ} (ha : Tendsto a l (nhds 0))
    (hmoment : ∀ᶠ i in l, ∀ x, (∫ y, (g.edist x y).toReal ∂μ i x) ≤ a i) :
    TendstoUniformly (fun i x ↦ ∫ y, f y ∂μ i x) f l := by
  have hLa : Tendsto (fun i ↦ L * a i) l (nhds 0) := by
    simpa using ha.const_mul L
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hmoment, hLa.eventually (gt_mem_nhds hε)] with i hi hεi
  intro x
  rw [Real.dist_eq, abs_sub_comm]
  exact ((g.abs_integral_sub_le_integral_distance hf hLip x (μ i x) (hμ i x)).trans
    (mul_le_mul_of_nonneg_left (hi x) hL)).trans_lt hεi

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

open Set Poincare.Analysis.Heat

set_option backward.isDefEq.respectTransparency false in


theorem heat_gradient_bound_of_gaussian_energy_of_initial_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M) {F : ℝ × M → ℝ} {k : ℝ}
    (hk : 0 ≤ k)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    (hRic : ∀ t ∈ Ioo 0 1, ∀ x,
      -k * g.inner x (D.gradient (fun y ↦ F (t, y)) x)
        (D.gradient (fun y ↦ F (t, y)) x) ≤
      D.ricci x (D.gradient (fun y ↦ F (t, y)) x)
        (D.gradient (fun y ↦ F (t, y)) x))
    (hqc : ContinuousOn (fun p : ℝ × M ↦ g.inner p.2
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      (D.gradient (fun y ↦ F (p.1, y)) p.2)) (Icc 0 1 ×ˢ univ))
    {B : ℝ}
    (hzero : ∀ x, g.inner x (D.gradient (fun y ↦ F (0, y)) x)
      (D.gradient (fun y ↦ F (0, y)) x) ≤ B ^ 2)
    (hi : Integrable (fun p : ℝ × M ↦ Real.exp (-(1 / 32 : ℝ) * (g.edist O p.2).toReal ^ 2) *
      g.inner p.2 (D.gradient (fun y ↦ F (p.1, y)) p.2)
        (D.gradient (fun y ↦ F (p.1, y)) p.2))
      ((volume.restrict (Ioc 0 1)).prod g.volumeMeasure)) :
    ∀ t ∈ Icc 0 1, ∀ x,
      g.tangentNorm x (D.gradient (fun y ↦ F (t, y)) x) ≤
        Real.sqrt (B ^ 2 + 1) * Real.exp k := by
  let q : ℝ × M → ℝ := fun p ↦ g.inner p.2
    (D.gradient (fun y ↦ F (p.1, y)) p.2) (D.gradient (fun y ↦ F (p.1, y)) p.2)
  let z : ℝ × M → ℝ := fun p ↦
    Real.exp (-k * p.1) * Real.sqrt (q p + 1) - Real.sqrt (B ^ 2 + 1)
  have hq0 (p : ℝ × M) : 0 ≤ q p := by
    by_cases h : D.gradient (fun y ↦ F (p.1, y)) p.2 = 0
    · simp [q, h]
    · exact (g.pos p.2 _ h).le
  have hFg (t : ℝ) (ht : 0 < t) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x) :=
    hF.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hzs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ z (Ioo 0 1 ×ˢ univ) := by
    intro p hp
    have hq := D.contMDiffAt_gradient_normSq_spacetime (hFg p.1 hp.1.1 p.2)
    have hs := (Real.contDiffAt_sqrt (by linarith [hq0 p] : q p + 1 ≠ 0)).contMDiffAt.comp p
      (hq.add contMDiffAt_const)
    exact ((((Real.contDiff_exp : ContDiff ℝ ∞ Real.exp).contMDiff.contMDiffAt.comp p
      (contMDiffAt_const.mul contMDiffAt_fst)).mul hs).sub contMDiffAt_const).contMDiffWithinAt
  have hzc : ContinuousOn z (Icc 0 1 ×ˢ univ) :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn).mul
      (Real.continuous_sqrt.comp_continuousOn (hqc.add continuousOn_const))).sub continuousOn_const
  have hzi : Integrable (fun p : ℝ × M ↦ Real.exp (-(1 / 32 : ℝ) * (g.edist O p.2).toReal ^ 2) *
      max (z p) 0 ^ 2) ((volume.restrict (Ioc 0 1)).prod g.volumeMeasure) := by
    have hmc : ContinuousOn (fun p : ℝ × M ↦
        Real.exp (-(1 / 32 : ℝ) * (g.edist O p.2).toReal ^ 2) * max (z p) 0 ^ 2)
        (Icc 0 1 ×ˢ (Set.univ : Set M)) := by
      exact (((Real.continuous_exp.comp
        ((continuous_const (y := -(1 / 32 : ℝ))).mul
          (((g.continuous_toReal_edist O).comp continuous_snd).pow 2))).continuousOn).mul
        ((hzc.sup (continuousOn_const (c := (0 : ℝ)))).pow 2))
    have hm := hmc.aemeasurable
        (μ := volume.prod g.volumeMeasure) (measurableSet_Icc.prod MeasurableSet.univ)
    have hm' := hm.mono_set (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
    rw [← Measure.prod_restrict, Measure.restrict_univ] at hm'
    apply hi.mono' hm'.aestronglyMeasurable
    have ht : ∀ᵐ p : ℝ × M ∂(volume.restrict (Ioc 0 1)).prod g.volumeMeasure,
        p.1 ∈ Ioc 0 1 := Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [ht] with p hp
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply regularized_norm_excess_sq_le (hq0 p)
    · exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hk hp.1.le])
    · exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg B])
  have hz := D.karpLi_nonpos_on_short_interval hcomplete O (by norm_num : (0 : ℝ) < 1 / 32)
    zero_lt_one (by norm_num) hzs hzc
    (fun t ht x ↦ D.normalized_regularized_gradient_subsolution
      (hFg t ht.1) (hheat t ht.1) hk x (hRic t ht x)) ?_ hzi
  · intro t ht x
    have hx := hz t ht x
    have he : Real.sqrt (q (t, x) + 1) ≤ Real.sqrt (B ^ 2 + 1) * Real.exp (k * t) := by
      have hx' : Real.exp (-k * t) * Real.sqrt (q (t, x) + 1) ≤ Real.sqrt (B ^ 2 + 1) := by
        change z (t, x) ≤ 0 at hx
        dsimp only [z] at hx
        linarith
      have hm := mul_le_mul_of_nonneg_left hx' (Real.exp_pos (k * t)).le
      rw [← mul_assoc, ← Real.exp_add] at hm
      simpa [mul_comm, mul_left_comm, mul_assoc] using hm
    change Real.sqrt (q (t, x)) ≤ _
    calc
      _ ≤ Real.sqrt (q (t, x) + 1) := Real.sqrt_le_sqrt (by linarith)
      _ ≤ Real.sqrt (B ^ 2 + 1) * Real.exp (k * t) := he
      _ ≤ Real.sqrt (B ^ 2 + 1) * Real.exp k := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [ht.2])) (Real.sqrt_nonneg _)
  · intro x
    change Real.exp (-k * 0) * Real.sqrt (q (0, x) + 1) - Real.sqrt (B ^ 2 + 1) ≤ 0
    simp only [mul_zero, Real.exp_zero, one_mul, sub_nonpos]
    exact Real.sqrt_le_sqrt (by have := hzero x; change q (0, x) ≤ B ^ 2 at this; linarith)



theorem heat_gradient_bound_of_gaussian_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M) {F : ℝ × M → ℝ} {k : ℝ}
    (hk : 0 ≤ k)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    (hRic : ∀ t ∈ Ioo 0 1, ∀ x,
      -k * g.inner x (D.gradient (fun y ↦ F (t, y)) x)
        (D.gradient (fun y ↦ F (t, y)) x) ≤
      D.ricci x (D.gradient (fun y ↦ F (t, y)) x)
        (D.gradient (fun y ↦ F (t, y)) x))
    (hqc : ContinuousOn (fun p : ℝ × M ↦ g.inner p.2
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      (D.gradient (fun y ↦ F (p.1, y)) p.2)) (Icc 0 1 ×ˢ univ))
    (hzero : ∀ x, g.inner x (D.gradient (fun y ↦ F (0, y)) x)
      (D.gradient (fun y ↦ F (0, y)) x) ≤ 4)
    (hi : Integrable (fun p : ℝ × M ↦ Real.exp (-(1 / 32 : ℝ) * (g.edist O p.2).toReal ^ 2) *
      g.inner p.2 (D.gradient (fun y ↦ F (p.1, y)) p.2)
        (D.gradient (fun y ↦ F (p.1, y)) p.2))
      ((volume.restrict (Ioc 0 1)).prod g.volumeMeasure)) :
    ∀ t ∈ Icc 0 1, ∀ x,
      g.tangentNorm x (D.gradient (fun y ↦ F (t, y)) x) ≤ Real.sqrt 5 * Real.exp k := by
  simpa only [show (2 : ℝ) ^ 2 + 1 = 5 by norm_num] using
    D.heat_gradient_bound_of_gaussian_energy_of_initial_bound hcomplete O hk hF hheat hRic hqc
      (B := 2) (by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hzero) hi

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

open Set




theorem kernel_evolution_gradient_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    {g : RiemannianMetric n M} (H : ConservativeHeatKernelData g)
    (hn : 1 ≤ n) (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |H.connection.sectionalCurvature x v w| ≤ K)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hgrad : ∀ x, g.tangentNorm x (H.connection.gradient f x) ≤ 2)
    (O : M) (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (H.connection.laplacian (fun y ↦ F (t, y)) x) t)
    (hrep : ∀ t, 0 < t → ∀ x,
      F (t, x) = ∫ y, f y * H.kernel x y t ∂volumeMeasure g)
    (hzero : ∀ x, F (0, x) = f x)
    (hqc : ContinuousOn (fun p : ℝ × M ↦ g.inner p.2
      (H.connection.gradient (fun y ↦ F (p.1, y)) p.2)
      (H.connection.gradient (fun y ↦ F (p.1, y)) p.2)) (Icc 0 1 ×ˢ univ))
    {V c : ℝ} (hV : 0 ≤ V)
    (hvol : ∀ R : ℝ, 1 ≤ R →
      (g.volumeMeasure {x | (g.edist O x).toReal ≤ R}).toReal ≤ V * Real.exp (c * R)) :
    ∀ t ∈ Icc 0 1, ∀ x,
      g.tangentNorm x (H.connection.gradient (fun y ↦ F (t, y)) x) ≤
        Real.sqrt 5 * Real.exp (((n : ℝ) - 1) * K) := by
  have hLip : ∀ x y, |f y - f x| ≤ 2 * (g.edist x y).toReal := by
    intro x y
    rw [abs_sub_comm]
    exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound
      (hf.of_le (by simp)) (K := (2 : ℝ≥0)) (by norm_num)
      (fun z ↦ (H.connection.gradient_norm_le_iff f z (by norm_num)).mp (hgrad z)) x y
  apply H.connection.heat_gradient_bound_of_gaussian_energy hcomplete O
    (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hn)) hK) hF hheat ?_ hqc ?_
    (H.integrable_gaussian_kernel_evolution_energy hcomplete hf.continuous
      (by norm_num) hLip O happrox hF hheat hrep hzero hV (by norm_num) hvol)
  · intro t ht x
    simpa only [neg_mul] using
      H.connection.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le
        x K (hsec x) (H.connection.gradient (fun y ↦ F (t, y)) x)
  · intro x
    have he : (fun y ↦ F (0, y)) = f := funext hzero
    rw [he]
    have hnorm := hgrad x
    have hnonneg : 0 ≤ g.inner x (H.connection.gradient f x) (H.connection.gradient f x) := by
      by_cases h : H.connection.gradient f x = 0
      · simp [h]
      · exact (g.pos x _ h).le
    change Real.sqrt _ ≤ 2 at hnorm
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg
      (g.inner x (H.connection.gradient f x) (H.connection.gradient f x))]

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
