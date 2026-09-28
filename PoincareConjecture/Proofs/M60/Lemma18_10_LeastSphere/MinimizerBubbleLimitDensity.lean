import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessTarget
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessWeakLimit



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

local instance suBubbleDensityBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suBubbleDensityBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem gram_eq_reader
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) 1 e) (p : M)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] E)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (z : LoopPlane)
    (hz : f z ∈ (extChartAt (𝓡 n) p).source)
    (hread : (fun q => L (e q)) =ᶠ[𝓝 (f z)] (extChartAt (𝓡 n) p)) (i j : Fin 2) :
    m60AreaGram g f z i j =
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (L (e (f z)))
        (L (fderiv ℝ (e ∘ f) z (b i))) (L (fderiv ℝ (e ∘ f) z (b j))) := by
  let c := extChartAt (𝓡 n) p
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c (f z) :=
    (contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [extChartAt_source] using hz)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z hc (hf.mdifferentiable (by simp) z)
  rw [mfderiv_eq_fderiv] at hd
  have hcol (v : LoopPlane) : fderiv ℝ (c ∘ f) z v =
      mfderiv (𝓡 n) (𝓡 n) c (f z) (mfderiv (𝓡 2) (𝓡 n) f z v) :=
    congrArg (fun A => A v) hd
  have hobs : DifferentiableAt ℝ (e ∘ f) z :=
    ((contMDiff_iff_contDiff.mp (he.comp hf)).differentiable_one z)
  have hfun : (fun y => L (e (f y))) =ᶠ[𝓝 z] c ∘ f :=
    hread.comp_tendsto hf.continuous.continuousAt
  have hdr : fderiv ℝ (c ∘ f) z = L.comp (fderiv ℝ (e ∘ f) z) :=
    hfun.fderiv_eq.symm.trans (L.hasFDerivAt.comp z hobs.hasFDerivAt).fderiv
  have hpair := ConjugateVariation.chartCoefficients_apply g p hz
    (mfderiv (𝓡 2) (𝓡 n) f z (b i)) (mfderiv (𝓡 2) (𝓡 n) f z (b j))
  rw [← hcol (b i), ← hcol (b j), hdr] at hpair
  change g.pullbackCoefficients c.symm (c (f z))
    (L (fderiv ℝ (e ∘ f) z (b i))) (L (fderiv ℝ (e ∘ f) z (b j))) =
      m60AreaGram g f z i j at hpair
  rw [← hread.self_of_nhds] at hpair
  exact hpair.symm




theorem suObserved_density_tendsto
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) 1 e) (hei : IsClosedEmbedding e)
    (hread : SUChartReadable (n := n) e)
    (f : ℕ → LoopPlane → M) (f0 : LoopPlane → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    (hf0 : ContMDiff (𝓡 2) (𝓡 n) 1 f0) (z : LoopPlane)
    (hv : Tendsto (fun j => e (f j z)) atTop (𝓝 (e (f0 z))))
    (hd : Tendsto (fun j => fderiv ℝ (e ∘ f j) z) atTop (𝓝 (fderiv ℝ (e ∘ f0) z))) :
    Tendsto (fun j => m60AreaDensity g (f j) z) atTop (𝓝 (m60AreaDensity g f0 z)) ∧
      Tendsto (fun j => m60EnergyDensity g (f j) z) atTop (𝓝 (m60EnergyDensity g f0 z)) := by
  obtain ⟨p, hp, L, hL⟩ := hread (f0 z)
  let c := extChartAt (𝓡 n) p
  let G := g.pullbackCoefficients c.symm
  have hval : Tendsto (fun j => f j z) atTop (𝓝 (f0 z)) :=
    hei.isEmbedding.tendsto_nhds_iff.mpr hv
  have hchart : ∀ᶠ j in atTop, f j z ∈ c.source :=
    hval ((isOpen_extChartAt_source p).mem_nhds hp)
  have htail : ∀ᶠ j in atTop, (fun q => L (e q)) =ᶠ[𝓝 (f j z)] c :=
    hval hL.eventually_nhds
  let J := EuclideanSpace ℝ (Fin d) × (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin d))
  let j0 : J := (e (f0 z), fderiv ℝ (e ∘ f0) z)
  have hL0 : L (e (f0 z)) = c (f0 z) := hL.self_of_nhds
  have hG : ContinuousAt G (L (e (f0 z))) := by
    rw [hL0]
    exact ((g.contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (c.map_source hp))).continuousAt
  have hLj : ContinuousAt (fun j : J => L j.1) j0 :=
    (L.continuous.comp (continuous_fst : Continuous (fun j : J => j.1))).continuousAt
  have hGj : ContinuousAt (fun j : J => G (L j.1)) j0 :=
    hG.comp_of_eq hLj rfl
  have hVj (i : Fin 2) : ContinuousAt (fun j : J => L (j.2 (b i))) j0 :=
    L.continuous.continuousAt.comp (continuousAt_snd.clm_apply continuousAt_const)
  have hgram (i j : Fin 2) :
      Tendsto (fun k => m60AreaGram g (f k) z i j) atTop (𝓝 (m60AreaGram g f0 z i j)) := by
    have hh := ((hGj.clm_apply (hVj i)).clm_apply (hVj j)).tendsto.comp (hv.prodMk_nhds hd)
    change Tendsto (fun k => G (L (e (f k z)))
      (L (fderiv ℝ (e ∘ f k) z (b i))) (L (fderiv ℝ (e ∘ f k) z (b j)))) atTop
      (𝓝 (G (L (e (f0 z)))
        (L (fderiv ℝ (e ∘ f0) z (b i))) (L (fderiv ℝ (e ∘ f0) z (b j))))) at hh
    rw [← gram_eq_reader g e he p L f0 hf0 z hp hL i j] at hh
    apply hh.congr'
    filter_upwards [hchart, htail] with k hk hkr
    exact (gram_eq_reader g e he p L (f k) (hf k) z hk hkr i j).symm
  constructor
  · have hh := ((hgram 0 0).mul (hgram 1 1)).sub ((hgram 0 1).mul (hgram 1 0))
    simpa only [m60AreaDensity, Matrix.det_fin_two, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_const_nhds.max hh)
  · simpa only [m60EnergyDensity, Matrix.trace_fin_two] using
      ((hgram 0 0).add (hgram 1 1)).const_mul (1 / 2 : ℝ)




theorem suObserved_disk_integrals_tendsto
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) 1 e) (hei : IsClosedEmbedding e)
    (hread : SUChartReadable (n := n) e)
    (f : ℕ → LoopPlane → M) (f0 : LoopPlane → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    (hf0 : ContMDiff (𝓡 2) (𝓡 n) 1 f0)
    (hv : TendstoLocallyUniformly (fun j => e ∘ f j) (e ∘ f0) atTop)
    (hd : TendstoLocallyUniformly (fun j => fderiv ℝ (e ∘ f j)) (fderiv ℝ (e ∘ f0)) atTop)
    {B : ℝ} (hbound : ∀ j z, m60EnergyDensity g (f j) z ≤ B)
    (center : LoopPlane) (R : ℝ) :
    Tendsto (fun j => ∫ z in Metric.ball center R, m60AreaDensity g (f j) z) atTop
        (𝓝 (∫ z in Metric.ball center R, m60AreaDensity g f0 z)) ∧
      Tendsto (fun j => ∫ z in Metric.ball center R, m60EnergyDensity g (f j) z) atTop
        (𝓝 (∫ z in Metric.ball center R, m60EnergyDensity g f0 z)) := by
  let mu := volume.restrict (Metric.ball center R)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have ht (z : LoopPlane) := suObserved_density_tendsto g e he hei hread f f0 hf hf0 z
    (hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))
    (hd.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))
  constructor
  · apply tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun j => (m60AreaDensity_continuous g (hf j)).aestronglyMeasurable) (integrable_const _)
    · intro j
      filter_upwards [] with z
      rw [Real.norm_of_nonneg (m60AreaDensity_nonneg g (f j) z)]
      exact (m60AreaDensity_le_energyDensity g (f j) z).trans (hbound j z)
    · exact Eventually.of_forall fun z => (ht z).1
  · apply tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun j => (m60EnergyDensity_continuous g (hf j)).aestronglyMeasurable) (integrable_const _)
    · intro j
      filter_upwards [] with z
      rw [Real.norm_of_nonneg (m60EnergyDensity_nonneg g (f j) z)]
      exact hbound j z
    · exact Eventually.of_forall fun z => (ht z).2




theorem suObserved_total_energy_le
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) 1 e) (hei : IsClosedEmbedding e)
    (hread : SUChartReadable (n := n) e)
    (f : ℕ → LoopPlane → M) (f0 : LoopPlane → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    (hf0 : ContMDiff (𝓡 2) (𝓡 n) 1 f0)
    (hv : TendstoLocallyUniformly (fun j => e ∘ f j) (e ∘ f0) atTop)
    (hd : TendstoLocallyUniformly (fun j => fderiv ℝ (e ∘ f j)) (fderiv ℝ (e ∘ f0)) atTop)
    (hi : ∀ j, Integrable (m60EnergyDensity g (f j))) {I : ℝ}
    (henergy : Tendsto (fun j => ∫ z, m60EnergyDensity g (f j) z) atTop (𝓝 I)) :
    Integrable (m60EnergyDensity g f0) ∧ (∫ z, m60EnergyDensity g f0 z) ≤ I := by
  have hp (z : LoopPlane) := (suObserved_density_tendsto g e he hei hread f f0 hf hf0 z
    (hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))
    (hd.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))).2
  have hn (j : ℕ) : (∫⁻ z, ‖m60EnergyDensity g (f j) z‖ₑ) =
      ENNReal.ofReal (∫ z, m60EnergyDensity g (f j) z) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi j)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => Real.norm_of_nonneg (m60EnergyDensity_nonneg g (f j) z)
  have ht : Tendsto (fun j => ∫⁻ z, ‖m60EnergyDensity g (f j) z‖ₑ) atTop
      (𝓝 (ENNReal.ofReal I)) := by
    simpa only [hn, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp henergy
  have hfat : (∫⁻ z, ‖m60EnergyDensity g f0 z‖ₑ) ≤ ENNReal.ofReal I := by
    calc
      _ = ∫⁻ z, liminf (fun j => ‖m60EnergyDensity g (f j) z‖ₑ) atTop :=
        lintegral_congr fun z => (hp z).enorm.liminf_eq.symm
      _ ≤ liminf (fun j => ∫⁻ z, ‖m60EnergyDensity g (f j) z‖ₑ) atTop :=
        lintegral_liminf_le' (fun j => (hi j).aestronglyMeasurable.aemeasurable.enorm)
      _ = ENNReal.ofReal I := ht.liminf_eq
  have h0 : Integrable (m60EnergyDensity g f0) :=
    ⟨(m60EnergyDensity_continuous g hf0).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.mpr (hfat.trans_lt ENNReal.ofReal_lt_top)⟩
  have hI : 0 ≤ I := ge_of_tendsto henergy (Eventually.of_forall fun j =>
    integral_nonneg (m60EnergyDensity_nonneg g (f j)))
  rw [← ofReal_integral_norm_eq_lintegral_enorm h0] at hfat
  have hnorm : (∫ z, ‖m60EnergyDensity g f0 z‖) = ∫ z, m60EnergyDensity g f0 z :=
    integral_congr_ae (Eventually.of_forall fun z =>
      Real.norm_of_nonneg (m60EnergyDensity_nonneg g f0 z))
  rw [hnorm] at hfat
  exact ⟨h0, (ENNReal.ofReal_le_ofReal_iff hI).mp hfat⟩

end PoincareConjecture.M60
